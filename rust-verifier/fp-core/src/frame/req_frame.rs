//! The layout file and the request's frame builder, ported from `blocks/frame/req_frame.h`
//! (lines 30-163).
//!
//! From the arrays (named matrices) that a request's sub-proofs declare and a layout file, this
//! builds the request's segments (`ReqShape::link`, iop/req.rs) and their arrays' layout
//! (`ReqLayout`, iop/req_rows.rs). Prover and verifier declare the arrays separately and share
//! this code.
//!
//! A segment (`link` in identifiers) is one sub-proof's part of a request's proof; a commit point
//! (`moment`) is a prover message of a segment that commits arrays. The layout file
//! (`layout.txt`, written by prover/tools/pack_layout.py) places each array in the rows of one
//! oracle message. Blank lines and lines beginning with `#` are skipped. Segments, commit points
//! and groups are numbered from 1; arrays, rows and places from 0.
//!   a group:   link moment group class rows life
//!   a block:   link moment group array R a K e low row place br bj 0
//! A group is one oracle message of its commit point. Class N: rows over F. Class B: rows over F,
//! kept for `life` later segments to read; other classes have life 0. Class W: rows over E.
//! `layout_read()` and `req_frame()` return null or an error string; neither exits on a file's
//! content. The result must still pass `req_fault()` and `req_layout_fault()`: nothing here checks
//! that blocks are aligned, stay inside their array and group, do not overlap and cover their
//! arrays.

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::iop::foldeq::E_DEGREE;
use crate::iop::laid::{LaidBlock, LaidMatrix};
use crate::iop::req::{ReqLink, ReqMessage, ReqShape};
use crate::iop::req_rows::{ReqArray, ReqLayout};
use crate::iop::relation::OracleShape;

/// The default number of rows or columns of an array (`FrameArray`, req_frame.h:30-35): 1.
pub const FRAME_ARRAY_DEFAULT_SIZE: u64 = 1;

/// An array as its sub-proof declares it (`FrameArray`, req_frame.h:30-35).
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(non_snake_case)] // the C++ field is `over_E`
pub struct FrameArray {
    pub name: String,
    pub rows: u64,
    pub columns: u64,
    /// Its elements are in E: it is stored in rows over E; else in rows over F.
    pub over_E: bool,
    /// The last segment to read it is this many after its own; 0: only its own.
    pub life: u32,
}

impl Default for FrameArray {
    /// The C++ member defaults (req_frame.h:32-34): one row and one column, over F, no life.
    fn default() -> Self {
        FrameArray {
            name: String::new(),
            rows: FRAME_ARRAY_DEFAULT_SIZE,
            columns: FRAME_ARRAY_DEFAULT_SIZE,
            over_E: false,
            life: 0,
        }
    }
}

/// A segment as its sub-proof declares it (`FrameLink`, req_frame.h:36-39).
#[derive(Clone, Debug, Default)]
pub struct FrameLink {
    pub name: String,
    /// `[moment][the array's number in the layout file]`.
    pub moment: Vec<Vec<FrameArray>>,
}

/// A group line (`LayoutGroup`, req_frame.h:57-62).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LayoutGroup {
    /// All three are counted from 0 here.
    pub link: u32,
    pub moment: u32,
    pub group: u32,
    /// 'N', 'B' or 'W'.
    pub cls: u8,
    pub rows: u64,
    pub life: u32,
}

impl Default for LayoutGroup {
    /// The C++ member defaults (req_frame.h:58-61): 'N', no rows, no life.
    fn default() -> Self {
        LayoutGroup { link: 0, moment: 0, group: 0, cls: b'N', rows: 0, life: 0 }
    }
}

/// A block line (`LayoutBlock`, req_frame.h:63-66).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LayoutBlock {
    pub link: u32,
    pub moment: u32,
    pub group: u32,
    pub array: u32,
    pub at: LaidBlock,
}

impl Default for LayoutBlock {
    /// The C++ member defaults, with a default `LaidBlock`.
    fn default() -> Self {
        LayoutBlock { link: 0, moment: 0, group: 0, array: 0, at: LaidBlock::default() }
    }
}

/// The lines of one layout file (`LayoutLines`, req_frame.h:67-70).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LayoutLines {
    pub groups: Vec<LayoutGroup>,
    pub blocks: Vec<LayoutBlock>,
}

// ---------------------------------------------------------------------------------------------------------------------
// The parser
// ---------------------------------------------------------------------------------------------------------------------

/// `isspace` in the C locale: space, `\t`, `\n`, `\v`, `\f`, `\r`.
fn is_space(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

/// The whitespace of a blank line, exactly as `std::string::find_first_not_of(" \t\r")` sees it.
fn is_blank(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\r')
}

/// A scanner over one line with the conversion rules of `std::sscanf`'s `%llu`, `%c` and the
/// format's spaces. `%llu` skips whitespace, accepts a sign and leading zeros (a negative value
/// wraps modulo 2^64; an overlong one saturates, as glibc's `strtoull` does); `%c` reads exactly
/// one character after the format's space has skipped whitespace.
struct Scan<'a> {
    line: &'a [u8],
    at: usize,
}

impl<'a> Scan<'a> {
    fn new(line: &'a [u8]) -> Self {
        Scan { line, at: 0 }
    }

    fn skip_space(&mut self) {
        while self.at < self.line.len() && is_space(self.line[self.at]) {
            self.at += 1;
        }
    }

    /// `%llu`. None if no digit follows the optional sign.
    fn u64(&mut self) -> Option<u64> {
        self.skip_space();
        let mut negative = false;
        if self.at < self.line.len() && (self.line[self.at] == b'+' || self.line[self.at] == b'-') {
            negative = self.line[self.at] == b'-';
            self.at += 1;
        }
        let start = self.at;
        let mut value: u64 = 0;
        while self.at < self.line.len() && self.line[self.at].is_ascii_digit() {
            value = value
                .saturating_mul(10)
                .saturating_add((self.line[self.at] - b'0') as u64);
            self.at += 1;
        }
        if self.at == start {
            return None;
        }
        Some(if negative { 0u64.wrapping_sub(value) } else { value })
    }

    /// `%c` after a space in the format.
    fn ch(&mut self) -> Option<u8> {
        self.skip_space();
        if self.at < self.line.len() {
            let c = self.line[self.at];
            self.at += 1;
            Some(c)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct BlockFields {
    link: u64,
    moment: u64,
    group: u64,
    array: u64,
    r: u64,
    a: u64,
    k: u64,
    e: u64,
    c: u8,
    row: u64,
    place: u64,
    br: u64,
    bj: u64,
    sj: u64,
    tail: u8,
}

#[derive(Clone, Copy, Debug, Default)]
struct GroupFields {
    link: u64,
    moment: u64,
    group: u64,
    c: u8,
    rows: u64,
    life: u64,
    tail: u8,
}

/// `sscanf(line, "%llu %llu %llu %llu %llu %llu %llu %llu %c %llu %llu %llu %llu %llu %c", ...)`,
/// returning the number of conversions that succeeded (0 to 15).
fn scan_block(line: &[u8]) -> (usize, BlockFields) {
    let mut s = Scan::new(line);
    let mut f = BlockFields::default();
    let mut n = 0usize;
    macro_rules! num {
        ($slot:ident) => {
            match s.u64() {
                Some(x) => {
                    f.$slot = x;
                    n += 1;
                }
                None => return (n, f),
            }
        };
    }
    num!(link);
    num!(moment);
    num!(group);
    num!(array);
    num!(r);
    num!(a);
    num!(k);
    num!(e);
    match s.ch() {
        Some(c) => {
            f.c = c;
            n += 1;
        }
        None => return (n, f),
    }
    num!(row);
    num!(place);
    num!(br);
    num!(bj);
    num!(sj);
    match s.ch() {
        Some(t) => {
            f.tail = t;
            n += 1;
        }
        None => return (n, f),
    }
    (n, f)
}

/// `sscanf(line, "%llu %llu %llu %c %llu %llu %c", ...)`, returning the number of conversions
/// that succeeded (0 to 7).
fn scan_group(line: &[u8]) -> (usize, GroupFields) {
    let mut s = Scan::new(line);
    let mut f = GroupFields::default();
    let mut n = 0usize;
    macro_rules! num {
        ($slot:ident) => {
            match s.u64() {
                Some(x) => {
                    f.$slot = x;
                    n += 1;
                }
                None => return (n, f),
            }
        };
    }
    num!(link);
    num!(moment);
    num!(group);
    match s.ch() {
        Some(c) => {
            f.c = c;
            n += 1;
        }
        None => return (n, f),
    }
    num!(rows);
    num!(life);
    match s.ch() {
        Some(t) => {
            f.tail = t;
            n += 1;
        }
        None => return (n, f),
    }
    (n, f)
}

/// Reads a layout file (`layout_read`, req_frame.h:72-104). Checks each line by itself. `%llu`
/// also accepts a sign and leading zeros, so one layout has many spellings, each with another
/// configuration digest. Null, or the error string.
pub fn layout_read(text: &str, out: &mut LayoutLines) -> Option<&'static str> {
    *out = LayoutLines::default();
    let bytes = text.as_bytes();
    let mut at = 0usize;
    while at < bytes.len() {
        let mut end = at;
        while end < bytes.len() && bytes[end] != b'\n' {
            end += 1;
        }
        let line = &bytes[at..end];
        at = end + 1;
        if line.iter().all(|&c| is_blank(c)) || line.first() == Some(&b'#') {
            continue;
        }
        let (n, f) = scan_block(line);
        if n == 14 {
            if f.link == 0
                || f.moment == 0
                || f.group == 0
                || f.link >> 20 != 0
                || f.moment >> 20 != 0
                || f.group >> 20 != 0
                || f.array >> 20 != 0
            {
                return Some("a block's line has a link, moment or group 0 (they are counted from 1), or a number of 2^20 or more");
            }
            if (f.c != b'r' && f.c != b'c')
                || f.sj != 0
                || f.a >= 48
                || f.e >= 48
                || f.br >= 48
                || f.bj >= 48
            {
                return Some("a block's line has another letter than r or c, a last number that is not 0, or a logarithm of 48 or more");
            }
            out.blocks.push(LayoutBlock {
                link: f.link as u32 - 1,
                moment: f.moment as u32 - 1,
                group: f.group as u32 - 1,
                array: f.array as u32,
                at: LaidBlock {
                    first_i: f.r,
                    bits_i: f.a as u32,
                    first_c: f.k,
                    bits_c: f.e as u32,
                    i_is_low: f.c == b'r',
                    first_row: f.row,
                    first_place: f.place,
                    row_bits: f.br as u32,
                    place_bits: f.bj as u32,
                },
            });
        } else {
            let (n, g) = scan_group(line);
            if n == 6 {
                if g.link == 0
                    || g.moment == 0
                    || g.group == 0
                    || g.link >> 20 != 0
                    || g.moment >> 20 != 0
                    || g.group >> 20 != 0
                {
                    return Some("a group's line has a link, moment or group 0 (they are counted from 1), or a number of 2^20 or more");
                }
                if (g.c != b'N' && g.c != b'B' && g.c != b'W')
                    || g.rows == 0
                    || g.rows >> 32 != 0
                    || g.life >> 20 != 0
                    || (g.life != 0) != (g.c == b'B')
                {
                    return Some("a group's line has another class than N, B, W, no rows or 2^32 or more, or a life that does not go with its class (B alone has one)");
                }
                out.groups.push(LayoutGroup {
                    link: g.link as u32 - 1,
                    moment: g.moment as u32 - 1,
                    group: g.group as u32 - 1,
                    cls: g.c,
                    rows: g.rows,
                    life: g.life as u32,
                });
            } else {
                return Some("a line is neither a group's nor a block's");
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------------------------------------------------
// The frame
// ---------------------------------------------------------------------------------------------------------------------

/// Fills `shape.link` and `layout`, checking the file against the declared arrays; the rest of the
/// shape is the caller's (`req_frame`, req_frame.h:106-163). Set `shape.code` and `shape.mask_code`
/// first: each oracle message copies them. Each `ReqLink::plain` is reset to 0. `answers`: the
/// number of answers to each oracle message's out-of-domain sample; `req_fault()` requires
/// `shape.answers` to equal it.
pub fn req_frame(
    links: &[FrameLink],
    file: &LayoutLines,
    answers: u32,
    shape: &mut ReqShape,
    layout: &mut ReqLayout,
) -> Option<&'static str> {
    shape.link.clear();
    layout.link.clear();
    // `[link][moment][group]`: the oracle message's number in its link.
    let mut message: Vec<Vec<Vec<usize>>> = Vec::new();
    for l in links {
        shape.link.push(ReqLink {
            name: l.name.clone(),
            messages: Vec::new(),
            plain: 0,
        });
        layout.link.push(Vec::new());
        message.push(vec![Vec::new(); l.moment.len()]);
    }
    for g in &file.groups {
        let li = g.link as usize;
        let mi = g.moment as usize;
        if li >= links.len() || mi >= links[li].moment.len() {
            return Some("a group lies in a link or a moment that the request does not have");
        }
        {
            let sent = &shape.link[li].messages;
            if g.group as usize != message[li][mi].len() {
                return Some("the groups of a moment are not numbered in turn");
            }
            if let Some(last) = sent.last() {
                if last.moment > g.moment {
                    return Some("the moments of a link do not come in turn");
                }
            }
        }
        if li + 1 < links.len() && !shape.link[li + 1].messages.is_empty() {
            return Some("the links do not come in turn");
        }
        let sent = &mut shape.link[li].messages;
        if sent.is_empty() && g.life != 0 {
            return Some("the first oracle message of a link holds its mask row and cannot be kept");
        }
        let m = ReqMessage {
            shape: OracleShape {
                name: format!(
                    "{}, moment {}, group {}",
                    links[li].name,
                    g.moment + 1,
                    g.group + 1
                ),
                code: shape.code,
                main_rows: g.rows as usize,
                main_deg: if g.cls == b'W' { E_DEGREE as u32 } else { 1 },
                // The segment's mask row.
                mask_rows: if sent.is_empty() { 1 } else { 0 },
                mask_code: shape.mask_code,
                answers,
            },
            leaf_class: 0,
            moment: g.moment,
            life: g.life,
        };
        message[li][mi].push(sent.len());
        sent.push(m);
    }
    // `[link][moment][array]`: its number in layout.link[link], or none yet.
    let mut array: Vec<Vec<Vec<usize>>> = Vec::new();
    for l in links {
        let mut moments = Vec::new();
        for m in &l.moment {
            moments.push(vec![usize::MAX; m.len()]);
        }
        array.push(moments);
    }
    for b in &file.blocks {
        let li = b.link as usize;
        let mi = b.moment as usize;
        let gi = b.group as usize;
        let ai = b.array as usize;
        if li >= links.len() || mi >= links[li].moment.len() || gi >= message[li][mi].len() {
            return Some("a block lies in a group that the file does not have");
        }
        if ai >= links[li].moment[mi].len() {
            return Some("a block belongs to an array that its moment does not have");
        }
        if array[li][mi][ai] == usize::MAX {
            let a = &links[li].moment[mi][ai];
            let in_ = &shape.link[li].messages[message[li][mi][gi]];
            if (in_.shape.main_deg == E_DEGREE as u32) != a.over_E {
                return Some("an array over E lies in rows over F, or an array over F in rows over E");
            }
            if in_.life < a.life {
                return Some("an array is kept for fewer links than its last reader is on");
            }
            array[li][mi][ai] = layout.link[li].len();
            layout.link[li].push(ReqArray {
                name: a.name.clone(),
                message: message[li][mi][gi],
                laid: LaidMatrix {
                    size_i: a.rows,
                    size_c: a.columns,
                    blocks: Vec::new(),
                },
            });
        }
        let at = array[li][mi][ai];
        let a = &mut layout.link[li][at];
        if a.message != message[li][mi][gi] {
            return Some("an array lies in two groups");
        }
        a.laid.blocks.push(b.at);
    }
    for l in 0..links.len() {
        for m in &array[l] {
            for &at in m {
                if at == usize::MAX {
                    return Some("an array has no block");
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn read(text: &str) -> Result<LayoutLines, &'static str> {
        let mut out = LayoutLines::default();
        match layout_read(text, &mut out) {
            None => Ok(out),
            Some(e) => Err(e),
        }
    }

    fn frame_links() -> Vec<FrameLink> {
        vec![FrameLink {
            name: String::from("link one"),
            moment: vec![vec![FrameArray {
                name: String::from("a"),
                rows: 1,
                columns: 4,
                over_E: false,
                life: 0,
            }]],
        }]
    }

    #[test]
    fn layout_read_takes_group_and_block_lines() {
        let out = read("1 1 1 N 4 0\n1 1 1 0 0 2 0 0 r 0 0 2 0 0\n").unwrap();
        assert_eq!(out.groups.len(), 1);
        assert_eq!(out.blocks.len(), 1);
        let g = &out.groups[0];
        assert_eq!((g.link, g.moment, g.group), (0, 0, 0));
        assert_eq!((g.cls, g.rows, g.life), (b'N', 4, 0));
        let b = &out.blocks[0];
        assert_eq!((b.link, b.moment, b.group, b.array), (0, 0, 0, 0));
        assert_eq!((b.at.first_i, b.at.bits_i, b.at.bits_c), (0, 2, 0));
        assert!(b.at.i_is_low);
        assert_eq!((b.at.first_row, b.at.first_place), (0, 0));
        assert_eq!((b.at.row_bits, b.at.place_bits), (2, 0));
    }

    #[test]
    fn layout_read_skips_blank_and_comment_lines() {
        let out = read("\n \t\r\n# a comment\n1 1 1 W 2 0\r\n").unwrap();
        assert_eq!(out.groups.len(), 1);
        assert_eq!(out.groups[0].cls, b'W');
        assert!(out.blocks.is_empty());
    }

    #[test]
    fn layout_read_accepts_signs_and_leading_zeros() {
        let out = read("+01 01 01 N 04 0\n").unwrap();
        let g = &out.groups[0];
        assert_eq!((g.link, g.moment, g.group, g.rows), (0, 0, 0, 4));
        let out = read("1 1 1 0 -1 0 0 0 c 0 0 0 0 0\n").unwrap();
        assert_eq!(out.blocks[0].at.first_i, u64::MAX);
        assert!(!out.blocks[0].at.i_is_low);
    }

    #[test]
    fn layout_read_rejects_wrong_field_counts() {
        let bad = "a line is neither a group's nor a block's";
        assert_eq!(read("1 1 1 N 4\n"), Err(bad));
        assert_eq!(read("1 1 1 N 4 0 x\n"), Err(bad));
        assert_eq!(read("1 1 1 0 0 2 0 0 r 0\n"), Err(bad));
    }

    #[test]
    fn layout_read_checks_the_class_and_life_rules() {
        let bad = "a group's line has another class than N, B, W, no rows or 2^32 or more, or a life that does not go with its class (B alone has one)";
        assert_eq!(read("1 1 1 B 4 0\n"), Err(bad));
        assert_eq!(read("1 1 1 N 4 1\n"), Err(bad));
        assert_eq!(read("1 1 1 X 4 0\n"), Err(bad));
        assert_eq!(read("1 1 1 N 0 0\n"), Err(bad));
        assert!(read("1 1 1 B 4 2\n").is_ok());
    }

    #[test]
    fn layout_read_checks_the_block_rules() {
        let bad = "a block's line has another letter than r or c, a last number that is not 0, or a logarithm of 48 or more";
        assert_eq!(read("1 1 1 0 0 2 0 0 x 0 0 2 0 0\n"), Err(bad));
        assert_eq!(read("1 1 1 0 0 2 0 0 r 0 0 2 0 1\n"), Err(bad));
        assert_eq!(read("1 1 1 0 0 48 0 0 r 0 0 0 0 0\n"), Err(bad));
        assert_eq!(
            read("0 1 1 0 0 2 0 0 r 0 0 2 0 0\n"),
            Err("a block's line has a link, moment or group 0 (they are counted from 1), or a number of 2^20 or more")
        );
    }

    fn shape() -> ReqShape {
        ReqShape { code: 0, mask_code: 0, ..ReqShape::default() }
    }

    #[test]
    fn req_frame_builds_the_link_and_its_arrays() {
        let file = read("1 1 1 N 4 0\n1 1 1 0 0 2 0 0 r 0 0 2 0 0\n").unwrap();
        let mut shape = shape();
        let mut layout = ReqLayout::default();
        assert_eq!(req_frame(&frame_links(), &file, 1, &mut shape, &mut layout), None);
        assert_eq!(shape.link.len(), 1);
        assert_eq!(shape.link[0].name, "link one");
        assert_eq!(shape.link[0].messages.len(), 1);
        assert_eq!(shape.link[0].moments(), 1);
        let m = &shape.link[0].messages[0];
        assert_eq!(m.shape.name, "link one, moment 1, group 1");
        assert_eq!(
            (m.shape.main_rows, m.shape.main_deg, m.shape.mask_rows),
            (4, 1, 1)
        );
        assert_eq!((m.shape.code, m.shape.mask_code, m.shape.answers), (0, 0, 1));
        assert_eq!((m.leaf_class, m.moment, m.life), (0, 0, 0));
        assert_eq!(layout.link.len(), 1);
        assert_eq!(layout.link[0].len(), 1);
        let a = &layout.link[0][0];
        assert_eq!(a.name, "a");
        assert_eq!(a.message, 0);
        assert_eq!((a.laid.size_i, a.laid.size_c), (1, 4));
        assert_eq!(a.laid.blocks.len(), 1);
        assert_eq!(layout.find(0, "a").unwrap().message, 0);
        assert!(layout.find(1, "a").is_none());
    }

    #[test]
    fn req_frame_rejects_a_kept_first_message() {
        let file = read("1 1 1 B 4 1\n").unwrap();
        let mut shape = shape();
        let mut layout = ReqLayout::default();
        assert_eq!(
            req_frame(&frame_links(), &file, 1, &mut shape, &mut layout),
            Some("the first oracle message of a link holds its mask row and cannot be kept")
        );
    }

    #[test]
    fn req_frame_rejects_groups_out_of_turn() {
        let file = read("1 1 2 N 4 0\n").unwrap();
        let mut shape = shape();
        let mut layout = ReqLayout::default();
        assert_eq!(
            req_frame(&frame_links(), &file, 1, &mut shape, &mut layout),
            Some("the groups of a moment are not numbered in turn")
        );
    }

    #[test]
    fn req_frame_rejects_an_array_without_a_block() {
        let file = read("1 1 1 N 4 0\n").unwrap();
        let mut shape = shape();
        let mut layout = ReqLayout::default();
        assert_eq!(
            req_frame(&frame_links(), &file, 1, &mut shape, &mut layout),
            Some("an array has no block")
        );
    }

    #[test]
    fn req_frame_rejects_an_array_in_a_group_that_is_not_there() {
        let file = read("1 1 1 N 4 0\n1 1 2 0 0 2 0 0 r 0 0 2 0 0\n").unwrap();
        let mut shape = shape();
        let mut layout = ReqLayout::default();
        assert_eq!(
            req_frame(&frame_links(), &file, 1, &mut shape, &mut layout),
            Some("a block lies in a group that the file does not have")
        );
    }

    #[test]
    fn req_frame_checks_the_array_field_and_life() {
        let file = read("1 1 1 W 4 0\n1 1 1 0 0 2 0 0 r 0 0 2 0 0\n").unwrap();
        let mut shape = shape();
        let mut layout = ReqLayout::default();
        assert_eq!(
            req_frame(&frame_links(), &file, 1, &mut shape, &mut layout),
            Some("an array over E lies in rows over F, or an array over F in rows over E")
        );
    }
}
