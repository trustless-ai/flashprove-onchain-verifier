//! A request's arrays and their public layout, ported from `blocks/iop/req_rows.h`
//! (lines 26-102).
//!
//! A sub-proof works on arrays: named matrices of committed entries. A public layout cuts each
//! array into aligned blocks and places them in the main rows of one of the segment's oracle
//! messages (`LaidMatrix`, laid.h). Prover and verifier share the layout, which is input to a
//! verifier; the verifier must call `req_layout_fault()` first.
//!
//! The verifier also builds each segment's linear claim from the segment's equation
//! (`req_row()`, req_rows.h:104-169, the `ReqRows` class). The C++ class keeps references to the
//! context, frame and layout; the port passes them in, so `ChainCheck` can hold one mutable
//! verifier context without a self-reference.

use alloc::string::String;
use alloc::vec::Vec;

use super::laid::{laid_form, laid_ok, LaidMatrix};
use super::relation::{Codes, OracleShape, Part, Row, Statement};
use super::req::{ReqFrame, ReqShape};
use super::send_pad::send_pad;
use crate::chain::public::PublicBytes;
use crate::field::ext::E;
use crate::iop::laid::IndexWeights;
use crate::iop::message::Writer;
use crate::numbers::codes::ceil_log2;

/// One array of a segment (`ReqArray`, req_rows.h:26-30).
#[derive(Clone, Debug, Default)]
pub struct ReqArray {
    pub name: String,
    /// Which of its segment's oracle messages contains it.
    pub message: usize,
    /// Its size and its blocks; rows are numbered within that oracle message.
    pub laid: LaidMatrix,
}

/// The arrays of one request (`ReqLayout`, req_rows.h:31-40). `link[l]`: the arrays that segment
/// l sends.
#[derive(Clone, Debug, Default)]
pub struct ReqLayout {
    pub link: Vec<Vec<ReqArray>>,
}

impl ReqLayout {
    /// `ReqLayout::find()` (req_rows.h:34-39).
    pub fn find(&self, l: usize, name: &str) -> Option<&ReqArray> {
        if l < self.link.len() {
            for a in &self.link[l] {
                if a.name == name {
                    return Some(a);
                }
            }
        }
        None
    }
}

impl PublicBytes for ReqArray {
    /// `public_bytes(Writer&, const ReqArray&)` (req_rows.h:44-46).
    fn public_bytes(&self, w: &mut Writer) {
        self.name.public_bytes(w);
        w.put_u64(self.message as u64);
        w.put_u64(self.laid.size_i);
        w.put_u64(self.laid.size_c);
        w.put_u64(self.laid.blocks.len() as u64);
        for b in &self.laid.blocks {
            b.public_bytes(w);
        }
    }
    /// `public_fault(const ReqArray&)` (req_rows.h:49-54).
    fn public_fault(&self) -> Option<&'static str> {
        public_fault_array(self)
    }
}

impl PublicBytes for ReqLayout {
    /// `public_bytes(Writer&, const ReqLayout&)` (req_rows.h:47).
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.link.len() as u64);
        for link in &self.link {
            w.put_u64(link.len() as u64);
            for a in link {
                a.public_bytes(w);
            }
        }
    }
    /// `public_fault(const ReqLayout&)` (req_rows.h:55-63).
    fn public_fault(&self) -> Option<&'static str> {
        public_fault_layout(self)
    }
}

/// Null, or what is wrong with one array by itself (`public_fault(const ReqArray&)`,
/// req_rows.h:49-54).
pub fn public_fault_array(a: &ReqArray) -> Option<&'static str> {
    if a.name.is_empty() {
        return Some("an array has no name");
    }
    if a.laid.size_i == 0 || a.laid.size_c == 0 || a.laid.size_i >> 48 != 0 || a.laid.size_c >> 48 != 0 {
        return Some("an array has no element, or 2^48 rows or columns or more");
    }
    if a.laid.blocks.is_empty() {
        return Some("an array has no block");
    }
    for b in &a.laid.blocks {
        if let Some(fault) = b.public_fault() {
            return Some(fault);
        }
    }
    None
}

/// Null, or what is wrong with the layout by itself (`public_fault(const ReqLayout&)`,
/// req_rows.h:55-63).
pub fn public_fault_layout(l: &ReqLayout) -> Option<&'static str> {
    for link in &l.link {
        for a in 0..link.len() {
            if let Some(fault) = public_fault_array(&link[a]) {
                return Some(fault);
            }
            for b in 0..a {
                if link[a].name == link[b].name {
                    return Some("two arrays of a link have one name");
                }
            }
        }
    }
    None
}

/// Null if the layout fits shape `s` and the codes, else what is wrong (`req_layout_fault`,
/// req_rows.h:65-102). A layout is input to a verifier, which must call this first. Precondition,
/// not checked: `req_fault(codes, s)` is null. This repeats only part of `public_fault_layout()`:
/// an empty name passes.
pub fn req_layout_fault(codes: &Codes, s: &ReqShape, layout: &ReqLayout) -> Option<&'static str> {
    if layout.link.len() != s.link.len() {
        return Some("the layout has another number of links than the request");
    }
    for l in 0..s.link.len() {
        let messages = &s.link[l].messages;
        {
            let arrays = &layout.link[l];
            for a in 0..arrays.len() {
                if arrays[a].message >= messages.len() {
                    return Some("an array lies in an oracle message that its link does not have");
                }
                for b in 0..a {
                    if arrays[a].name == arrays[b].name {
                        return Some("two arrays of a link have one name");
                    }
                }
            }
        }
        for (m, message) in messages.iter().enumerate() {
            let o: &OracleShape = &message.shape;
            let mut in_it: Vec<LaidMatrix> = Vec::new();
            for a in &layout.link[l] {
                if a.message == m {
                    in_it.push(a.laid.clone());
                }
            }
            if in_it.is_empty() {
                continue;
            }
            if o.main_rows == 0 {
                return Some("an array lies in an oracle message without main rows");
            }
            let row_bits = ceil_log2(o.main_rows as u64);
            let place_bits = codes.base[o.code as usize].log_ell();
            if !laid_ok(&in_it, row_bits, place_bits) {
                return Some("blocks that are not aligned, overlap, leave the table or do not cover their array");
            }
            for x in &in_it {
                for b in &x.blocks {
                    if b.first_row + (1u64 << b.row_bits) > o.main_rows as u64 {
                        return Some("a block lies in rows that are not sent");
                    }
                    // No claim may read the pad of a sample.
                    for p in send_pad(codes, o) {
                        let row = p.index & ((1u64 << row_bits) - 1);
                        let place = p.index >> row_bits;
                        if p.part == Part::Main
                            && row >= b.first_row
                            && row < b.first_row + (1u64 << b.row_bits)
                            && place >= b.first_place
                            && place < b.first_place + (1u64 << b.place_bits)
                        {
                            return Some("a block covers the pad of its oracle message's sample");
                        }
                    }
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------------------------------------------------
// A segment's equation
// ---------------------------------------------------------------------------------------------------------------------

/// One term: the weight `scale * on_rows[i] * on_columns[c]` on element `(i, c)` of the array
/// `array` (`ReqTerm`, req_rows.h:104-110).
#[derive(Clone, Debug)]
pub struct ReqTerm {
    /// The segment that sent the array: the current one or an earlier one.
    pub born: usize,
    pub array: String,
    pub scale: E,
    /// At most one of the two is a written-out vector.
    pub on_rows: IndexWeights,
    pub on_columns: IndexWeights,
}

impl Default for ReqTerm {
    /// The C++ member defaults (req_rows.h:106-109): `scale` is one.
    fn default() -> Self {
        ReqTerm {
            born: 0,
            array: String::new(),
            scale: E::one(),
            on_rows: IndexWeights::default(),
            on_columns: IndexWeights::default(),
        }
    }
}

/// Sum of `terms` + sum over i of `on_masks[i] * (mask entry i)` = `target` (`ReqEquation`,
/// req_rows.h:111-116).
#[derive(Clone, Debug, Default)]
pub struct ReqEquation {
    pub terms: Vec<ReqTerm>,
    /// Coefficients on the first entries of the segment's mask row.
    pub on_masks: Vec<E>,
    /// Public.
    pub target: E,
}

/// Builds a segment's linear claim (`ReqRows::row()`, req_rows.h:140-163). The caller adds it to
/// the segment's group (`frame.group()`). The process ends if an array's oracle message has not
/// been sent or the current segment cannot read it; that is for a program fault, not a bad proof.
pub fn req_row(frame: &ReqFrame, layout: &ReqLayout, S: &mut Statement, eq: &ReqEquation) -> Row {
    let shape = frame.shape();
    let mut row = Row::plain(alloc::format!(
        "equation of {}",
        shape.link[frame.link()].name
    ));
    for t in &eq.terms {
        let a = match layout.find(t.born, &t.array) {
            Some(a) => a,
            None => panic!("request: an equation names an array that the layout does not have"),
        };
        let o = frame.where_(t.born, a.message);
        row.add_form(
            o,
            laid_form(
                &a.laid.blocks,
                S.row_bits(o, Part::Main),
                S.place_bits(o, Part::Main),
                &t.on_rows,
                &t.on_columns,
                t.scale,
            ),
        );
    }
    if !eq.on_masks.is_empty() {
        let messages = &shape.link[frame.link()].messages;
        let mut m = 0usize;
        while m < messages.len() && messages[m].shape.mask_rows == 0 {
            m += 1;
        }
        assert!(
            m < messages.len() && messages[m].shape.mask_rows == 1,
            "request: coefficients on a mask row, and the link has not one"
        );
        let o = frame.where_(frame.link(), m);
        let taken = S.masks(o).take_n(eq.on_masks.len()); // used up
        assert!(
            taken.first().unwrap().index() == 0
                && taken.last().unwrap().index() + 1 == taken.len() as u32,
            "request: entries of the link's mask row were taken before its equation names them by number"
        );
        row.add_run(o, Part::Mask, 0, 1, eq.on_masks.clone());
    }
    row.target = eq.target;
    row
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use crate::code::code::Code;
    use crate::iop::iopp::{IoppChoice, IoppStage};
    use crate::iop::laid::LaidBlock;
    use crate::iop::req::{ReqLink, ReqMessage};

    fn codes() -> Codes {
        Codes { base: vec![Code { log_n: 8, ell: 256, r: 0 }], mask: Vec::new() }
    }

    fn shape() -> ReqShape {
        ReqShape {
            code: 0,
            mask_code: 0,
            link: vec![ReqLink {
                name: String::from("link"),
                messages: vec![ReqMessage {
                    shape: OracleShape {
                        name: String::from("message"),
                        code: 0,
                        main_rows: 4,
                        main_deg: 1,
                        mask_rows: 0,
                        mask_code: 0,
                        answers: 1,
                    },
                    leaf_class: 0,
                    moment: 0,
                    life: 0,
                }],
                plain: 0,
            }],
            at_start: Vec::new(),
            answers: 1,
            last: vec![
                IoppStage { code: 0, mask_code: 0, k: 1, h: 0 },
                IoppStage { code: 0, mask_code: 0, k: 0, h: 0 },
            ],
            choice: IoppChoice::default(),
        }
    }

    fn layout(block: LaidBlock) -> ReqLayout {
        ReqLayout {
            link: vec![vec![ReqArray {
                name: String::from("a"),
                message: 0,
                laid: LaidMatrix { size_i: 1, size_c: 4, blocks: vec![block] },
            }]],
        }
    }

    /// The whole 1x4 array in one table row, across 2^place_bits places.
    fn whole_array(row_bits: u32, place_bits: u32) -> LaidBlock {
        LaidBlock {
            first_i: 0,
            first_c: 0,
            first_row: 0,
            first_place: 0,
            bits_i: 0,
            bits_c: 2,
            row_bits,
            place_bits,
            i_is_low: true,
        }
    }

    #[test]
    fn req_layout_fault_accepts_an_aligned_layout() {
        assert_eq!(req_layout_fault(&codes(), &shape(), &layout(whole_array(0, 2))), None);
    }

    #[test]
    fn req_layout_fault_rejects_an_array_in_a_message_that_is_not_there() {
        let mut l = layout(whole_array(0, 2));
        l.link[0][0].message = 1;
        assert_eq!(
            req_layout_fault(&codes(), &shape(), &l),
            Some("an array lies in an oracle message that its link does not have")
        );
    }

    #[test]
    fn req_layout_fault_rejects_a_block_over_the_pad() {
        // The sample's pad of a 4-row message with one answer is at row 3, places 253-255.
        let mut block = whole_array(0, 2);
        block.first_row = 3;
        block.first_place = 252;
        assert_eq!(
            req_layout_fault(&codes(), &shape(), &layout(block)),
            Some("a block covers the pad of its oracle message's sample")
        );
    }

    #[test]
    fn req_layout_fault_rejects_blocks_that_do_not_cover_the_array() {
        let mut l = layout(whole_array(0, 2));
        l.link[0][0].laid.size_c = 8;
        assert_eq!(
            req_layout_fault(&codes(), &shape(), &l),
            Some("blocks that are not aligned, overlap, leave the table or do not cover their array")
        );
    }
}
