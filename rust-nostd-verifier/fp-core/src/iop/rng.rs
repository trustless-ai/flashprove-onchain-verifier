//! RNG, the approximate range check on committed cells, ported from the verifier's side of
//! `blocks/iop/rng.h` (lines 44-606).
//!
//! The prover's engine and its tables are not ported: `rng_prove` (rng.h:517-569), the write of a
//! matrix into a table (`laid_set`, rng.h:496-504) and the two helpers that fill a caller's tables
//! (`rng_lay_packed`/`rng_lay_reads`, rng.h:609-631). Everything that a verifier reaches is here:
//! the shape and its byte encoding and faults, the lookup's public inputs and layout, the claim on
//! the sent digits, the shape and weights checks, the plan check, Theta, the batched row and the
//! lookup's masks.
//!
//! Two deviations, both forced by the port's ownership and both in the manner of `LkpKeyClaim`:
//!
//! - `rng_theta` draws the entries before it calls `require_combinations`, because `close_bits`
//!   borrows the channel mutably in Rust while C++ keeps the handle usable. The two calls touch
//!   different state: `require_combinations` compares a number with the plan and draws nothing, so
//!   the order is observable only when the plan and the shape disagree, where both versions end
//!   the process. (`VerifierRounds::require_combinations` is a no-op once the channel has
//!   rejected the proof, as the C++ one is.)
//! - `RngOutput` cannot ask the channel in its destructor (`VerifierRounds` keeps its fate
//!   private, and the output may not borrow the channel). `rng_verify` marks the output rejected
//!   when it learns that the channel rejected the proof, as `LkpKeyClaim` does. A rejection that
//!   happens after `rng_verify` returned true is not seen: a drop after such a rejection ends the
//!   process here where C++ would let it pass. No honest run reaches either check.

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::Cell;

use super::context::{OracleNotice, VerifierContext};
use super::laid::{laid_form, laid_ok, IndexWeights, LaidBlock, LaidMatrix};
use super::lkp::{
    lkp_fault, lkp_live_blocks, lkp_on_block, lkp_verify, LkpKeyBlock, LkpKeys, LkpOutput,
    LkpPadding, LkpPlanesAt, LkpPublic, LkpTablePart,
};
use super::relation::{GroupId, OracleId, Part, Row, Statement, NONE_ID};
use super::send::{send_verify, AnswersRound};
use super::send_pad::send_pad;
use super::tensor::Tensor;
use crate::chain::public::{Public, PublicBytes};
use crate::chain::rounds::VerifierRounds;
use crate::field::ext::{F, E};
use crate::hash::calls::HashCalls;
use crate::iop::message::Writer;
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::Planned;
use crate::numbers::round_names::{R_BAT_SIGMA, R_RNG};

/// `F_BITS` (`blocks/field/field.h:23`), the number of bits of the base field.
const F_BITS: u32 = 64;

/// One matrix Y of cells, m rows by k columns, and where its packing is (rng.h:44-52).
///
/// The packed matrix, over F:
///   Pack(Y)[i'][c] = sum_(l < lanes) radix^l Y[lanes i' + l][c].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RngMatrix {
    /// Of the cells.
    pub rows: u64,
    pub columns: u64,
    /// The oracle message that holds the packed matrix.
    pub packed: OracleId,
    /// The packed matrix (`i` = packed row, `c` = column) in that message's main table.
    pub laid: Vec<LaidBlock>,
}

impl Default for RngMatrix {
    /// The C++ default of `packed` is `NONE_ID` (rng.h:50); Rust's derive would say 0.
    fn default() -> Self {
        RngMatrix { rows: 0, columns: 0, packed: NONE_ID, laid: Vec::new() }
    }
}

/// One read of the shape's matrix number `matrix`, under a public weight vector phi (rng.h:53-60).
///
/// Its table, over E:
///   Tab[c (m / L) + g] = sum_(i < L) phi[i] Y[g L + i][c].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RngRead {
    pub matrix: usize,
    /// L, its weight vector's length: divides the matrix's number of rows.
    pub length: u64,
}

/// The weights: phi, one vector for each read (rng.h:61-65). Not part of the shape.
pub type RngWeights = Vec<Vec<E>>;

/// The verifier's matrix Theta, entry by entry (rng.h:377).
pub type RngTheta = Vec<i8>;

/// What is public about one check, the weights apart (rng.h:66-125).
#[derive(Clone, Debug)]
pub struct RngShape {
    pub lanes: u32,
    pub log_radix: u32,
    pub digit_bits: [u32; 2],
    pub combinations: u32,
    pub matrices: Vec<RngMatrix>,
    pub reads: Vec<RngRead>,
    /// The oracle message that holds the reads' vector (none if there are no reads).
    pub reads_in: OracleId,
    /// That vector as a matrix with one row (`i` = 0, `c` = the entry's number).
    pub reads_laid: Vec<LaidBlock>,
    /// The digits' matrix has `i` = the combination u and `c` = the column: the low digit of cell
    /// row j (counted through all matrices) at c = j, the high digit at c = digit_columns + j.
    /// `digit_columns` is a power of two, at least `cell_rows()`.
    pub digit_columns: u64,
    /// The shape of the oracle message that RNG sends.
    pub digits: OracleNotice,
    /// In its main table.
    pub digits_laid: Vec<LaidBlock>,
    /// Of the lookup on the digits; sent with the digits. `rng_planes_at` fixes its layout.
    pub multiplicities: OracleNotice,
    /// The number that the digits' message gets on the channel; the multiplicities' message gets
    /// the next.
    pub digits_in: OracleId,
    /// The oracle message whose mask rows give the lookup's mask entries.
    pub masks_from: OracleId,
}

impl Default for RngShape {
    /// The C++ defaults of `lanes`, `reads_in`, `digits_in` and `masks_from` (rng.h:81-97);
    /// `OracleShape` keeps its own defaults for the two notices.
    fn default() -> Self {
        RngShape {
            lanes: 1,
            log_radix: 0,
            digit_bits: [0, 0],
            combinations: 0,
            matrices: Vec::new(),
            reads: Vec::new(),
            reads_in: NONE_ID,
            reads_laid: Vec::new(),
            digit_columns: 0,
            digits: OracleNotice { shape: Default::default(), leaf_class: 0 },
            digits_laid: Vec::new(),
            multiplicities: OracleNotice { shape: Default::default(), leaf_class: 0 },
            digits_in: NONE_ID,
            masks_from: NONE_ID,
        }
    }
}

impl RngShape {
    /// `RngShape::cell_rows` (rng.h:99-103).
    pub fn cell_rows(&self) -> u64 {
        let mut n = 0u64;
        for m in &self.matrices {
            n += m.rows;
        }
        n
    }

    /// `RngShape::all_columns` (rng.h:104-108).
    pub fn all_columns(&self) -> u64 {
        let mut n = 0u64;
        for m in &self.matrices {
            n += m.columns;
        }
        n
    }

    /// `RngShape::packed_rows` (rng.h:109).
    pub fn packed_rows(&self, mu: usize) -> u64 {
        (self.matrices[mu].rows + self.lanes as u64 - 1) / self.lanes as u64
    }

    /// `RngShape::read_entries` (rng.h:110).
    pub fn read_entries(&self, q: usize) -> u64 {
        let m = &self.matrices[self.reads[q].matrix];
        m.columns * (m.rows / self.reads[q].length)
    }

    /// Read q's first entry in the reads' vector; q = `reads.len()`: that vector's length
    /// (rng.h:111-115).
    pub fn read_first(&self, q: usize) -> u64 {
        let mut n = 0u64;
        for i in 0..q {
            n += self.read_entries(i);
        }
        n
    }

    /// Np: the smallest power of two >= N (rng.h:116).
    pub fn step(&self) -> u64 {
        1u64 << ceil_log2(self.combinations as u64)
    }

    /// How many equation numbers there are, unused ones included (rng.h:118-124).
    pub fn equations(&self) -> u64 {
        let mut n = 0u64;
        for mu in 0..self.matrices.len() {
            n += self.step() << ceil_log2(self.packed_rows(mu));
        }
        for r in &self.reads {
            n += self.step() * (self.matrices[r.matrix].rows / r.length);
        }
        n
    }
}

// ---- the shape's bytes and faults (rng.h:127-170) ----

impl PublicBytes for RngMatrix {
    /// Every field, in declaration order; every vector writes its length first
    /// (rng.h:128-130).
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.rows);
        w.put_u64(self.columns);
        w.put_u64(self.packed as u64);
        w.put_u64(self.laid.len() as u64);
        for b in &self.laid {
            b.public_bytes(w);
        }
    }
}

impl PublicBytes for RngRead {
    /// `public_bytes(Writer&, const RngRead&)` (rng.h:131).
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.matrix as u64);
        w.put_u64(self.length);
    }
}

impl PublicBytes for RngShape {
    /// Every field, in declaration order (rng.h:132-137).
    fn public_bytes(&self, w: &mut Writer) {
        for x in [
            self.lanes as u64,
            self.log_radix as u64,
            self.digit_bits[0] as u64,
            self.digit_bits[1] as u64,
            self.combinations as u64,
        ] {
            w.put_u64(x);
        }
        w.put_u64(self.matrices.len() as u64);
        for m in &self.matrices {
            m.public_bytes(w);
        }
        w.put_u64(self.reads.len() as u64);
        for r in &self.reads {
            r.public_bytes(w);
        }
        w.put_u64(self.reads_in as u64);
        w.put_u64(self.reads_laid.len() as u64);
        for b in &self.reads_laid {
            b.public_bytes(w);
        }
        w.put_u64(self.digit_columns);
        self.digits.public_bytes(w);
        w.put_u64(self.digits_laid.len() as u64);
        for b in &self.digits_laid {
            b.public_bytes(w);
        }
        self.multiplicities.public_bytes(w);
        w.put_u64(self.digits_in as u64);
        w.put_u64(self.masks_from as u64);
    }

    fn public_fault(&self) -> Option<&'static str> {
        rng_fault(self)
    }
}

/// Whether the shape is valid and consistent, as far as the object alone shows (rng.h:139-167).
///
/// RNG needs 4 D - 2 < radix and (4 D - 2)(1 + radix + .. + radix^(lanes - 1)) < p: then a packed
/// entry has at most one unpacking into integers in (-2 D, 2 D). The test on `window` implies both.
pub fn rng_fault(S: &RngShape) -> Option<&'static str> {
    if !(S.lanes >= 1 && S.combinations >= 1 && !S.matrices.is_empty()) {
        return Some("RNG: no lane, no combination or no matrix");
    }
    if !(S.lanes <= 64
        && S.log_radix < 64
        && S.digit_bits[0] < 64
        && S.digit_bits[1] < 64)
    {
        return Some("RNG: a number of the shape is out of range");
    }
    let window = S.digit_bits[0] + S.digit_bits[1]; // 2 D = 2^window
    if !(S.digit_bits[0] >= 1
        && S.digit_bits[1] >= 1
        && window + 1 <= S.log_radix
        && S.log_radix * (S.lanes - 1) + window + 2 < F_BITS)
    {
        return Some("RNG: the radix is too small for the window of the combinations, or a packed entry could wrap around in the field");
    }
    // Caps under which no product or sum of the shape's numbers wraps around a u64 in this file:
    // 2^24 rows, columns or combinations, 2^12 matrices or reads, 2^36 digit columns (rng.h:149-154).
    let most = 1u64 << 24;
    if !(S.combinations as u64 <= most
        && S.matrices.len() <= 4096
        && S.reads.len() <= 4096
        && S.digit_columns <= 1u64 << 36)
    {
        return Some("RNG: a number of the shape is out of range");
    }
    for m in &S.matrices {
        if !(m.rows >= 1 && m.columns >= 1 && m.rows <= most && m.columns <= most) {
            return Some("RNG: an empty matrix, or one with too many rows or columns");
        }
    }
    if !(S.cell_rows() <= S.digit_columns && (S.digit_columns & (S.digit_columns - 1)) == 0) {
        return Some("RNG: the digits' matrix has too few columns, or their number is no power of two");
    }
    for m in &S.matrices {
        if !S.reads.is_empty() && m.packed == S.reads_in {
            return Some("RNG: packed cells and reads in one oracle message are not served");
        }
    }
    for r in &S.reads {
        if !(r.matrix < S.matrices.len()
            && r.length >= 1
            && S.matrices[r.matrix].rows % r.length == 0)
        {
            return Some("RNG: a read of no matrix, or weights whose number does not divide the matrix's rows");
        }
    }
    if S.digits_in == NONE_ID || S.masks_from == NONE_ID || S.masks_from >= S.digits_in {
        return Some("RNG: the digits' message has no number, or the look-up's masks come from no earlier message");
    }
    for m in &S.matrices {
        if m.packed >= S.digits_in {
            return Some("RNG: packed cells in a message that comes no earlier than the digits");
        }
    }
    if !S.reads.is_empty() && S.reads_in >= S.digits_in {
        return Some("RNG: the reads in a message that comes no earlier than the digits");
    }
    None
}

/// `public_fault(const RngMatrix&)` (rng.h:168): a matrix is checked with the whole shape.
pub fn public_fault_matrix(_m: &RngMatrix) -> Option<&'static str> {
    None
}

/// `public_fault(const RngRead&)` (rng.h:169): a read is checked with the whole shape.
pub fn public_fault_read(_r: &RngRead) -> Option<&'static str> {
    None
}

// ---- the lookup's public inputs and layout (rng.h:172-239) ----

/// The lookup on the digits (rng.h:184-201).
///
/// LKP serves two functions, each with its own table: function 0 is the low digits, range 2^b0;
/// function 1 the high digits, range 2^b1. With DC = digit_columns, the digit of combination u in
/// column j < DC (y = 0 low, 1 high: the matrix's column j + DC y) is key number y + 2 (j + DC u).
/// The low bit y is LKP's tree number (`LkpPublic::g = 1`), and tree y belongs to function y. Key
/// numbers with N <= u < Np name no digit: they are padding, row 0 of the function's table.
pub fn rng_lookup(S: &RngShape) -> LkpPublic {
    let mut L = LkpPublic::default();
    let DC = S.digit_columns;
    let N = S.combinations as u64;
    let Np = S.step();
    L.parts = vec![1 + ceil_log2(DC) + ceil_log2(Np)];
    L.d = core::cmp::max(S.digit_bits[0], S.digit_bits[1]) + 1;
    let planes = L.parts[0] + 1; // the smallest number with 2^v < 2^planes, for 2^v keys
    L.mu = core::cmp::max(1, ceil_log2(planes as u64));
    L.live = if planes == 1u32 << L.mu { 0 } else { planes };
    L.g = 1;
    L.shifted = true;
    L.keys = vec![
        LkpKeyBlock { first: 0, log_trees: 0, function: 0, padding_row: 0 },
        LkpKeyBlock { first: 1, log_trees: 0, function: 1, padding_row: 0 },
    ];
    let half = 1u64 << (L.d - 1); // each function's table, repeated, fills half of the rows
    for f in 0..2u32 {
        let mut first = f as u64 * half;
        while first < (f as u64 + 1) * half {
            L.tables.push(LkpTablePart {
                first,
                log_rows: S.digit_bits[f as usize],
                function: f,
                rows: Vec::new(),
            });
            first += 1u64 << S.digit_bits[f as usize];
        }
    }
    if N < Np {
        for y in 0..2u64 {
            L.padding.push(LkpPadding {
                part: 0,
                first: y + 2 * DC * N,
                log_step: 1,
                length: DC * (Np - N),
                row: y * half,
            });
        }
    }
    L.read_from = vec![S.digits_in, S.digits_in + 1];
    L
}

/// Where the multiplicities are (rng.h:206): the live planes, in row 0 of their message's main
/// table, as a number of places within that row.
pub fn rng_planes_places(L: &LkpPublic) -> u64 {
    (L.planes() as u64) << L.d
}

/// The callback that adds the multiplicities' coefficients (rng.h:207-219).
///
/// A place is an index within a row. The block of planes `(first, bits)` of `lkp_live_blocks`
/// starts at place `first * 2^d`; within it the index is `(plane - first) + 2^bits * (row of the
/// lookup's table)`.
pub fn rng_planes_at(st: &Statement, S: &RngShape, L: &LkpPublic) -> LkpPlanesAt {
    let o = S.digits_in + 1;
    let row_bits = st.row_bits(o, Part::Main);
    let place_bits = st.table_bits(o, Part::Main) - row_bits;
    let mu = L.mu;
    let d = L.d;
    let planes = L.planes();
    Rc::new(move |row: &mut Row, v: Tensor| {
        for block in lkp_live_blocks(planes) {
            let mut part = lkp_on_block(&v, mu, block);
            let own = part.vars();
            part.insert_choice(own, place_bits - own, ((block.0 as u64) << d) >> own);
            part.insert_choice(0, row_bits, 0);
            row.add(o, Part::Main, part);
        }
    })
}

/// The claim that LKP leaves on its keys, as a linear claim on the sent digits (rng.h:222-239).
///
/// LKP's weights are product forms over the bits (y | j | u) of a key's number; `digits_laid`
/// places them.
pub fn rng_key_row(st: &Statement, S: &RngShape, mut keys: LkpKeys) -> Row {
    let bits_j = ceil_log2(S.digit_columns);
    let bits_u = ceil_log2(S.step());
    let row_bits = st.row_bits(S.digits_in, Part::Main);
    let place_bits = st.table_bits(S.digits_in, Part::Main) - row_bits;
    let mut row = Row::default();
    row.name = String::from("the digits at the point");
    assert!(keys.weights.entries.is_empty(), "RNG: weights that LKP has not made");
    for v in &keys.weights.tensors {
        assert!(
            !v.has_dense() && v.vars() == 1 + bits_j + bits_u,
            "RNG: weights that LKP has not made"
        );
        let mut on_u = IndexWeights::default();
        let mut on_column = IndexWeights::default();
        for t in 0..bits_j {
            on_column.lo.push(v.lo(1 + t));
            on_column.hi.push(v.hi(1 + t));
        }
        on_column.lo.push(v.lo(0)); // the matrix's column is j + DC y
        on_column.hi.push(v.hi(0));
        for t in 0..bits_u {
            on_u.lo.push(v.lo(1 + bits_j + t));
            on_u.hi.push(v.hi(1 + bits_j + t));
        }
        row.add_form(
            S.digits_in,
            laid_form(&S.digits_laid, row_bits, place_bits, &on_u, &on_column, v.scalar),
        );
    }
    row.target = keys.target;
    for m in core::mem::take(&mut keys.masks) {
        row.add_mask_term(m);
    }
    row
}

// ---- the checks (rng.h:241-330) ----

/// The checks on the shape that need the statement and the codes (rng.h:243-298). Both entry
/// points call it before Theta is drawn.
pub fn rng_shape_check(st: &Statement, S: &RngShape) {
    if let Some(fault) = rng_fault(S) {
        panic!("{}", fault);
    }
    for m in &S.matrices {
        assert!(
            st.oracle(m.packed).sampled,
            "RNG: an oracle message with packed cells has no answered sample"
        );
    }
    // The layouts: every element in exactly one block, no entry of a table with two elements.
    // A table has 2^ceil(log rows) row slots: the last may be rows of zeros that nobody sent.
    let in_sent_rows = |blocks: &[LaidBlock], s: &super::relation::OracleShape| -> bool {
        for b in blocks {
            if b.first_row + (1u64 << b.row_bits) > s.main_rows as u64 {
                return false;
            }
        }
        true
    };
    for mu in 0..S.matrices.len() {
        // All matrices of one oracle message together, when its first one comes.
        let mut first = true;
        for nu in 0..mu {
            first = first && S.matrices[nu].packed != S.matrices[mu].packed;
        }
        if !first {
            continue;
        }
        let mut together = Vec::new();
        for nu in mu..S.matrices.len() {
            if S.matrices[nu].packed == S.matrices[mu].packed {
                together.push(LaidMatrix {
                    size_i: S.packed_rows(nu),
                    size_c: S.matrices[nu].columns,
                    blocks: S.matrices[nu].laid.clone(),
                });
            }
        }
        let o = S.matrices[mu].packed;
        let row_bits = st.row_bits(o, Part::Main);
        let place_bits = st.table_bits(o, Part::Main) - row_bits;
        assert!(
            laid_ok(&together, row_bits, place_bits),
            "RNG: the packed matrices are not laid lawfully into their oracle message's table"
        );
        for x in &together {
            assert!(
                in_sent_rows(&x.blocks, &st.oracle(o).shape),
                "RNG: a block of a layout lies in a row that is not sent"
            );
        }
    }
    if !S.reads.is_empty() {
        assert!(
            st.oracle(S.reads_in).sampled,
            "RNG: the oracle message with the reads has no answered sample"
        );
        let row_bits = st.row_bits(S.reads_in, Part::Main);
        let place_bits = st.table_bits(S.reads_in, Part::Main) - row_bits;
        assert!(
            laid_ok(
                &[LaidMatrix {
                    size_i: 1,
                    size_c: S.read_first(S.reads.len()),
                    blocks: S.reads_laid.clone(),
                }],
                row_bits,
                place_bits,
            ),
            "RNG: the reads are not laid lawfully into their oracle message's table"
        );
        assert!(
            in_sent_rows(&S.reads_laid, &st.oracle(S.reads_in).shape),
            "RNG: a block of a layout lies in a row that is not sent"
        );
    }
    assert!(
        st.oracle(S.masks_from).sampled,
        "RNG: the oracle message that gives the look-up's mask entries has no answered sample"
    );
    let d = &S.digits.shape;
    let m = &S.multiplicities.shape;
    let codes = st.codes();
    assert!(
        d.main_rows >= 1
            && (d.code as usize) < codes.base.len()
            && laid_ok(
                &[LaidMatrix {
                    size_i: S.combinations as u64,
                    size_c: 2 * S.digit_columns,
                    blocks: S.digits_laid.clone(),
                }],
                ceil_log2(d.main_rows as u64),
                codes.base[d.code as usize].log_ell(),
            ),
        "RNG: the digits are not laid lawfully into their oracle message's table"
    );
    assert!(
        in_sent_rows(&S.digits_laid, d),
        "RNG: a block of a layout lies in a row that is not sent"
    );
    let L = rng_lookup(S);
    if let Some(fault) = lkp_fault(&L) {
        panic!("{}", fault);
    }
    assert!(
        m.main_rows >= 1
            && (m.code as usize) < codes.base.len()
            && rng_planes_places(&L) <= codes.base[m.code as usize].ell as u64,
        "RNG: the multiplicities do not fit row 0 of their oracle message's table"
    );
    // Digits and multiplicities cover no place of their message's pad, the random entries that
    // mask a sample's answer. (Without mask rows the pad is in the main rows: `send_pad`.)
    if d.answers != 0 && d.mask_rows == 0 {
        for p in send_pad(codes, d) {
            let bits = ceil_log2(d.main_rows as u64);
            let row = p.index & ((1u64 << bits) - 1);
            let place = p.index >> bits;
            for b in &S.digits_laid {
                assert!(
                    !(row >= b.first_row
                        && row < b.first_row + (1u64 << b.row_bits)
                        && place >= b.first_place
                        && place < b.first_place + (1u64 << b.place_bits)),
                    "RNG: the digits cover a place of their message's pad"
                );
            }
        }
    }
    if m.answers != 0 && m.mask_rows == 0 {
        for p in send_pad(codes, m) {
            let bits = ceil_log2(m.main_rows as u64);
            assert!(
                (p.index & ((1u64 << bits) - 1)) != 0
                    || p.index >> bits >= rng_planes_places(&L),
                "RNG: the multiplicities cover a place of their message's pad"
            );
        }
    }
}

/// The shape and the weights agree (rng.h:300-303).
pub fn rng_weights_check(S: &RngShape, phi: &RngWeights) {
    assert!(
        phi.len() == S.reads.len(),
        "RNG: not one weight vector for each read"
    );
    for q in 0..phi.len() {
        assert!(
            phi[q].len() as u64 == S.reads[q].length,
            "RNG: a read's weight vector has not the announced length"
        );
    }
}

/// The shape's N and the plan's N agree for every round named R_RNG (rng.h:305-330).
///
/// N is both in the shape, by which the block runs, and in the plan, which computes the error
/// 2^-N of Theta's round from it. Another N than that round's, or a plan that stores none, ends
/// the process when Theta is drawn (`require_combinations`).
pub fn rng_plan_fault(S: &RngShape, p: &Planned) -> Option<&'static str> {
    let mut planned = false;
    for r in &p.rounds {
        if r.name != R_RNG {
            continue;
        }
        planned = true;
        if S.combinations as u64 != r.combinations {
            return Some("RNG: the shape has another number of combinations than the plan prices the matrix's round with");
        }
    }
    if planned {
        None
    } else {
        Some("RNG: the plan has no round in which a matrix is drawn")
    }
}

// ---- Theta (rng.h:332-383) ----

/// Draws the verifier's matrix Theta, on both sides (rng.h:378-383).
///
/// Entry (column c of matrix mu, combination u) is at
/// `(first column of mu + c) * N + u`. An entry is 0 with probability 1/2, and 1 or -1 with
/// probability 1/4 each. The draw consumes the round named `R_RNG`; `require_combinations` ties
/// its N to the plan's.
///
/// The port draws before it asks `require_combinations`, because the C++ handle may use the
/// channel while `from` is alive and a Rust `BitsDraw` borrows it (module docs).
pub fn rng_theta(
    ch: &mut VerifierRounds<'_, '_, '_>,
    S: &RngShape,
    calls: &mut HashCalls,
) -> RngTheta {
    let n = (S.all_columns() * S.combinations as u64) as usize;
    let trits = {
        let mut from = ch.close_bits(R_RNG, calls);
        from.trits(n, calls)
    };
    ch.require_combinations(S.combinations as u64); // before an entry is drawn
    trits
}

// ---- the batched row (rng.h:385-473) ----

/// The linear claim that combines all of RNG's equations, equation number j under
/// `x^(first_power + j)` (rng.h:385-473).
///
/// There is one equation for each packed row i', or each part g of a read, and each combination u:
///   sum_c Theta[c][u] Pack(Y)[i'][c] = sum_l radix^l Psi[lanes i' + l][u]
///   sum_c Theta[c][u] Tab[c (m / L) + g] = sum_i phi[i] Psi[g L + i][u]
///
/// Numbering, with Np = step(): matrix mu has the numbers `first_mu + i' Np + u`, where first_mu is
/// the sum over the earlier matrices of Np * (their packed rows rounded up to a power of two).
/// After all matrices, the parts of all reads are counted through, s = 0, 1, .. (the reads in the
/// order of the list, g ascending within a read): part s has the numbers `first_reads + s Np + u`.
/// Numbers that name no equation stay unused.
///
/// The equations are never written out: the claim's weights are products. On a packed matrix:
/// powers of x^Np over i' times gx over c, where `gx[c] = sum_u x^u Theta[c][u]`. On the digits:
/// powers of x over u times a vector over the columns. On the reads: one vector.
///
/// `first_power` is C++'s default argument 0; a caller that has its own claims under the lower
/// powers passes their number.
pub fn rng_row(
    st: &Statement,
    S: &RngShape,
    phi: &RngWeights,
    theta: &RngTheta,
    digits: OracleId,
    x: &E,
    first_power: u64,
) -> Row {
    let N = S.combinations as u64;
    let Np = S.step();
    let power = |e: u64| -> E {
        let mut r = E::one();
        let mut s = *x;
        let mut e = e;
        while e != 0 {
            if e & 1 != 0 {
                r = r * s;
            }
            e >>= 1;
            s = s * s;
        }
        r
    };
    let x_step = power(Np);
    let mut x_to = vec![E::zero(); N as usize]; // x^u
    if N > 0 {
        x_to[0] = E::one();
        for u in 1..N as usize {
            x_to[u] = x_to[u - 1] * *x;
        }
    }
    let mut sum_x = E::zero();
    for p in &x_to {
        sum_x = sum_x + *p;
    }

    let mut row = Row::default();
    row.name = String::from("RNG");
    let mut on_digits = vec![E::zero(); (2 * S.digit_columns) as usize]; // low digits first
    let mut gx: Vec<Rc<Vec<E>>> = Vec::new(); // for each matrix, over its columns
    let mut first_cell_row: Vec<u64> = Vec::new();
    let mut number = first_power;
    let mut column = 0u64;
    let mut cell_row = 0u64;
    for mu in 0..S.matrices.len() {
        let m = &S.matrices[mu];
        let mut g = vec![E::zero(); m.columns as usize];
        for c in 0..m.columns {
            for u in 0..N {
                let t = theta[((column + c) * N + u) as usize];
                if t > 0 {
                    g[c as usize] = g[c as usize] + x_to[u as usize];
                }
                if t < 0 {
                    g[c as usize] = g[c as usize] - x_to[u as usize];
                }
            }
        }
        let g = Rc::new(g);
        gx.push(g.clone());
        let lead = power(number);
        let row_bits = st.row_bits(m.packed, Part::Main);
        let place_bits = st.table_bits(m.packed, Part::Main) - row_bits;
        row.add_form(
            m.packed,
            laid_form(
                &m.laid,
                row_bits,
                place_bits,
                &IndexWeights::powers(x_step, ceil_log2(S.packed_rows(mu))),
                &IndexWeights::written(g),
                lead,
            ),
        );
        let mut of_packed_row = lead;
        for i in 0..m.rows {
            if i != 0 && i % S.lanes as u64 == 0 {
                of_packed_row = of_packed_row * x_step;
            }
            let at = (cell_row + i) as usize;
            on_digits[at] = on_digits[at]
                - of_packed_row
                    * E::from_base(F::from_u64(
                        1u64 << (S.log_radix * ((i % S.lanes as u64) as u32)),
                    ));
        }
        first_cell_row.push(cell_row);
        number += Np << ceil_log2(S.packed_rows(mu));
        column += m.columns;
        cell_row += m.rows;
    }
    if !S.reads.is_empty() {
        let mut on_reads = vec![E::zero(); S.read_first(S.reads.len()) as usize];
        let mut lead = power(number);
        for q in 0..S.reads.len() {
            let r = &S.reads[q];
            let m = &S.matrices[r.matrix];
            let L = r.length;
            let parts = m.rows / L;
            for g in 0..parts {
                for c in 0..m.columns {
                    let at = (S.read_first(q) + c * parts + g) as usize;
                    on_reads[at] = on_reads[at] + lead * gx[r.matrix][c as usize];
                }
                for i in 0..L {
                    let at = (first_cell_row[r.matrix] + g * L + i) as usize;
                    on_digits[at] = on_digits[at] - lead * phi[q][i as usize];
                }
                lead = lead * x_step;
            }
        }
        let row_bits = st.row_bits(S.reads_in, Part::Main);
        let place_bits = st.table_bits(S.reads_in, Part::Main) - row_bits;
        let one = IndexWeights::default(); // the one row of the reads' vector
        row.add_form(
            S.reads_in,
            laid_form(
                &S.reads_laid,
                row_bits,
                place_bits,
                &one,
                &IndexWeights::written(Rc::new(on_reads)),
                E::one(),
            ),
        );
    }
    // Psi = lo + 2^b0 hi - D: the high digits get the low digits' weights times 2^b0, and D goes to
    // the right side.
    let mut all = E::zero();
    let high = E::from_base(F::from_u64(1u64 << S.digit_bits[0]));
    for j in 0..S.digit_columns {
        all = all + on_digits[j as usize];
        on_digits[(S.digit_columns + j) as usize] = high * on_digits[j as usize];
    }
    let row_bits = st.row_bits(digits, Part::Main);
    let place_bits = st.table_bits(digits, Part::Main) - row_bits;
    row.add_form(
        digits,
        laid_form(
            &S.digits_laid,
            row_bits,
            place_bits,
            &IndexWeights::powers(*x, ceil_log2(N)),
            &IndexWeights::written(Rc::new(on_digits)),
            E::one(),
        ),
    );
    row.target =
        E::from_base(F::from_u64(1u64 << (S.digit_bits[0] + S.digit_bits[1] - 1))) * sum_x * all;
    row
}

// ---- the entry points (rng.h:475-606) ----

/// What RNG leaves for `rng_row` (rng.h:475-492).
///
/// No honest run would reveal a missing claim, so the process ends if an output is dropped before
/// `rng_row_context` was called on it (`row_owed`), unless the channel has rejected the proof
/// meanwhile (module docs for what this port can see of the rejection). Whether the caller adds
/// the claim that `rng_row` returns to its group is not checked.
pub struct RngOutput {
    pub theta: RngTheta,
    /// As they were when Theta was drawn.
    pub phi: RngWeights,
    pub digits: OracleId,
    /// Of the lookup on the digits.
    pub shift: E,
    pub alpha: E,
    /// Copies of the claims that RNG added to the group (the lookup's, the one on its keys), for
    /// tests and reports.
    pub rows: Vec<Row>,
    pub row_owed: bool,
    rejected: Rc<Cell<bool>>,
}

impl Default for RngOutput {
    fn default() -> Self {
        RngOutput {
            theta: Vec::new(),
            phi: Vec::new(),
            digits: NONE_ID,
            shift: E::zero(),
            alpha: E::zero(),
            rows: Vec::new(),
            row_owed: false,
            rejected: Rc::new(Cell::new(false)),
        }
    }
}

impl Drop for RngOutput {
    fn drop(&mut self) {
        assert!(
            !self.row_owed || self.rejected.get(),
            "RNG: its output was dropped: the caller has made no row of its equations"
        );
    }
}

/// The verifier's side of RNG (rng.h:570-593).
///
/// False: the channel has rejected the proof. True alone decides nothing: RNG compares no value
/// from the proof; its claims in `group`, and the one that `rng_row_context` returns, are still to
/// be tested.
#[must_use]
pub fn rng_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    fixed: &Public<RngShape>,
    phi: &RngWeights,
    group: GroupId,
    out: &mut RngOutput,
    calls: &mut HashCalls,
) -> bool {
    let S = V.ch.get(fixed);
    rng_shape_check(&V.st, S);
    rng_weights_check(S, phi);
    let look = fixed.derive(rng_lookup);
    let L = V.ch.get(&look);
    out.phi = phi.clone();
    out.theta = rng_theta(V.ch, S, calls);
    let notices = vec![S.digits.clone(), S.multiplicities.clone()];
    let (good, ids) = send_verify(V, &notices, AnswersRound::Own, calls);
    if !good {
        return false;
    }
    assert!(
        ids.len() == 2 && ids[0] == S.digits_in && ids[1] == S.digits_in + 1,
        "RNG: the digits' message gets another number on the channel than the shape says"
    );
    out.digits = ids[0];
    V.st.join(group, ids[0], false);
    V.st.join(group, ids[1], false);
    out.row_owed = true;
    let planes = rng_planes_at(&V.st, S, L);
    let mut left = LkpOutput::default();
    if !lkp_verify(V, &look, &planes, S.masks_from, group, &mut left, NONE_ID, calls) {
        // C++'s `RngOutput` destructor asks the channel itself: only a rejection excuses a missing
        // row. LKP's contract says false is a rejection, but mirror the question, not the answer.
        if !V.ch.ok() {
            out.rejected.set(true);
        }
        return false;
    }
    out.shift = left.theta;
    out.alpha = left.alpha;
    out.rows = core::mem::take(&mut left.rows);
    let on_keys = rng_key_row(&V.st, S, left.keys.take(0));
    out.rows.push(on_keys.clone());
    V.st.add_row(group, on_keys);
    true
}

/// The batching of the equations (rng.h:594-606).
///
/// RNG draws the batching element x itself, so that it comes after the digits' sample and the
/// lookup, and has the channel compare the number of batched claims with the number that the
/// round's planned error counts. `rows_before`: claims of the caller's own under the lower powers
/// `1, x, .., x^(rows_before - 1)` of the same x, which is returned for them.
pub fn rng_row_context(
    ctx: &mut VerifierContext<'_, '_, '_, '_>,
    S: &Public<RngShape>,
    out: &mut RngOutput,
    x: &mut E,
    rows_before: u64,
    calls: &mut HashCalls,
) -> Row {
    assert!(
        out.row_owed,
        "RNG: its row has been made already, or RNG has not run"
    );
    // C++ calls `ctx.ch.get(S).equations()` while `from` is alive; Rust cannot hold that borrow
    // and the draw's at once. Reading the number first draws nothing.
    let equations = ctx.ch.get(S).equations();
    let mut from = ctx.ch.close_algebraic(R_BAT_SIGMA, calls);
    from.require_rows(rows_before + equations);
    *x = from.draw(calls);
    out.row_owed = false;
    let value = ctx.ch.get(S);
    rng_row(&ctx.st, value, &out.phi, &out.theta, out.digits, x, rows_before)
}
