//! LKP, the lookup argument by product trees, ported from the verifier's side of
//! `blocks/iop/lkp.h` (lines 163-390, 394-547, 549-677, 679-989, 1090-1137).
//!
//! The prover's engine (`LkpProver`, `LkpCpu`), its coins and its self-checks are not ported; the
//! public data, the checks, the summands, the verifier's rounds and the helpers that a test can
//! reach are. The C++ templates over `Side` are specialised to the verifier's side, and the hash
//! calls are explicit.
//!
//! Two deviations, both forced by the port's ownership: `LkpVerifierSide` names the two mask
//! oracle messages and takes their entries from the `Statement` one ledger at a time (C++ holds two
//! `MaskLedger&`), and `LkpKeyClaim` learns that the channel rejected the proof from `lkp_run`
//! (C++ asks the channel in its destructor; `VerifierRounds` keeps its fate private).

use alloc::boxed::Box;
use alloc::format;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::Cell;

use super::context::VerifierContext;
use super::hp::Weight;
use super::line::line;
use super::mask::{MaskSlot, MaskTerm};
use super::psc::{psc_masks, psc_verify, PscOutput};
use super::psc_rows::{point_row, psc_row_u, MapAt};
use super::relation::{GroupId, OracleId, Part, Row, Statement, NONE_ID};
use super::summand::{PointClaim, SumClaim, Summand};
use super::tensor::{Form, Tensor};
use crate::chain::public::{Public, PublicBytes};
use crate::chain::rounds::VerifierRounds;
use crate::field::ext::{F, E};
use crate::hash::calls::HashCalls;
use crate::iop::message::Writer;
use crate::numbers::round_names::{R_LKP, R_LKP_PLANES, R_LKP_SHIFT, R_ZERO};

/// `F_BITS` (`blocks/field/field.h:23`), the number of bits of the base field.
const F_BITS: u32 = 64;

/// One run of padding (`LkpPadding`, lkp.h:163-169): the key numbers `first + 2^log_step * i`,
/// `i < length`, of part `part` hold row `row` of the table (after the shift).
#[derive(Clone, Debug, Default)]
pub struct LkpPadding {
    pub part: u32,
    pub first: u64,
    pub log_step: u32,
    pub length: u64,
    pub row: u64,
}

/// A key block (`LkpKeyBlock`, lkp.h:173-178). The key number is `y + 2^g x`, `y < 2^g`; the keys
/// that share `y` form tree number `y`. `function == -1`: the trees are padding only.
#[derive(Clone, Debug)]
pub struct LkpKeyBlock {
    pub first: u64,
    pub log_trees: u32,
    pub function: i32,
    pub padding_row: u64,
}

impl Default for LkpKeyBlock {
    /// The C++ default of `function` is -1 (lkp.h:176); Rust's derive would say 0.
    fn default() -> Self {
        LkpKeyBlock { first: 0, log_trees: 0, function: -1, padding_row: 0 }
    }
}

/// One function's table inside the table (`LkpTablePart`, lkp.h:184-189).
#[derive(Clone, Debug, Default)]
pub struct LkpTablePart {
    pub first: u64,
    pub log_rows: u32,
    pub function: u32,
    /// Written out; empty: the range table `0, 1, .., 2^log_rows - 1`.
    pub rows: Vec<E>,
}

/// Everything public about one lookup (`LkpPublic`, lkp.h:217-248).
#[derive(Clone, Debug, Default)]
pub struct LkpPublic {
    /// `v_i`: part i of the keys has `2^(v_i)` entries; at least one part.
    pub parts: Vec<u32>,
    /// The table has `2^d` rows; each multiplicity has `w = 2^mu` bits.
    pub d: u32,
    pub mu: u32,
    /// How many of the `2^mu` plane slots are real; 0: all.
    pub live: u32,
    /// The low `h` bits of a row's number are its table part's number.
    pub h: u32,
    /// The low `g` bits of a key's number are its tree's number.
    pub g: u32,
    /// Function f's keys and rows are moved by `f * theta`.
    pub shifted: bool,
    /// All oracle messages from which the keys and the multiplicities are read.
    pub read_from: Vec<OracleId>,
    /// They tile the `2^g` tree numbers.
    pub keys: Vec<LkpKeyBlock>,
    /// They tile the `2^d` rows (a table may repeat to fill them).
    pub tables: Vec<LkpTablePart>,
    /// Strictly increasing by `(part, first)`; no two runs overlap.
    pub padding: Vec<LkpPadding>,
    /// The variables of the last key level that are bound first, in this order.
    pub last_key_level_order: Vec<u32>,
}

impl LkpPublic {
    /// `LkpPublic::planes` (lkp.h:241).
    pub fn planes(&self) -> u32 {
        if self.live != 0 {
            self.live
        } else {
            1u32 << self.mu
        }
    }
    /// `LkpPublic::part_bits` (lkp.h:242).
    pub fn part_bits(&self) -> &[u32] {
        &self.parts
    }
    /// `LkpPublic::all_keys` (lkp.h:243-247). After `lkp_public_check`: no wrap-around.
    pub fn all_keys(&self) -> u64 {
        let mut n = 0u64;
        for &x in &self.parts {
            n += 1u64 << x;
        }
        n
    }
    /// `planes()` (lkp.h:241), with the C++ spelling.
    #[allow(dead_code)]
    pub fn plane_slots(&self) -> u32 {
        self.planes()
    }
}

// ---- public bytes (lkp.h:250-265) ----

impl PublicBytes for LkpPadding {
    fn public_bytes(&self, w: &mut Writer) {
        for x in [
            self.part as u64,
            self.first,
            self.log_step as u64,
            self.length,
            self.row,
        ] {
            w.put_u64(x);
        }
    }
}

impl PublicBytes for LkpKeyBlock {
    fn public_bytes(&self, w: &mut Writer) {
        for x in [
            self.first,
            self.log_trees as u64,
            self.function as u64,
            self.padding_row,
        ] {
            w.put_u64(x);
        }
    }
}

impl PublicBytes for LkpTablePart {
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.first);
        w.put_u64(self.log_rows as u64);
        w.put_u64(self.function as u64);
        w.put_u64(self.rows.len() as u64);
        for x in &self.rows {
            w.put_e(*x);
        }
    }
}

impl PublicBytes for LkpPublic {
    /// Every field, in the order of its declaration; every vector writes its length first
    /// (blocks/chain/public.h:64-67).
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.parts.len() as u64);
        for x in &self.parts {
            w.put_u64(*x as u64);
        }
        for x in [
            self.d as u64,
            self.mu as u64,
            self.live as u64,
            self.h as u64,
            self.g as u64,
            self.shifted as u64,
        ] {
            w.put_u64(x);
        }
        w.put_u64(self.read_from.len() as u64);
        for x in &self.read_from {
            w.put_u64(*x as u64);
        }
        w.put_u64(self.keys.len() as u64);
        for x in &self.keys {
            x.public_bytes(w);
        }
        w.put_u64(self.tables.len() as u64);
        for x in &self.tables {
            x.public_bytes(w);
        }
        w.put_u64(self.padding.len() as u64);
        for x in &self.padding {
            x.public_bytes(w);
        }
        w.put_u64(self.last_key_level_order.len() as u64);
        for x in &self.last_key_level_order {
            w.put_u64(*x as u64);
        }
    }
    fn public_fault(&self) -> Option<&'static str> {
        lkp_fault(self)
    }
}

// ---- the shape and the checks (lkp.h:267-392) ----

/// What `lkp_run` works with (`LkpShape`, lkp.h:268-276).
#[derive(Clone)]
pub struct LkpShape {
    pub d: u32,
    pub mu: u32,
    pub planes: u32,
    pub part_bits: Vec<u32>,
    pub all_keys: u64,
    /// `(how many entries, the value that they hold)`
    pub padding: Vec<(u64, E)>,
    /// The extension of the table at a point of d coordinates (`std::function` in C++).
    pub table_at: Rc<dyn Fn(&[E]) -> E>,
    pub last_key_level_order: Vec<u32>,
}

impl Default for LkpShape {
    fn default() -> Self {
        LkpShape {
            d: 0,
            mu: 0,
            planes: 0,
            part_bits: Vec::new(),
            all_keys: 0,
            padding: Vec::new(),
            table_at: Rc::new(|_: &[E]| E::zero()),
            last_key_level_order: Vec::new(),
        }
    }
}

/// True if the whole lookup, a part of the keys or a function's block of trees is padding only
/// (`lkp_only_padding`, lkp.h:281-298). S has passed `lkp_fault`'s checks on blocks and runs.
pub fn lkp_only_padding(S: &LkpPublic) -> bool {
    let mut a_function = false;
    for b in &S.keys {
        a_function = a_function || b.function >= 0;
    }
    if !a_function {
        return true;
    }
    for part in 0..S.parts.len() {
        let mut padded = 0u64;
        for p in &S.padding {
            padded += if p.part as usize == part { p.length } else { 0 };
        }
        if (padded >> S.parts[part]) != 0 {
            return true;
        }
    }
    if S.parts.len() == 1 {
        // (tree numbers and key blocks are used with one part only)
        for b in &S.keys {
            if b.function < 0 {
                continue;
            }
            let mut padded = 0u64;
            for p in &S.padding {
                let same_tree =
                    ((p.first & ((1u64 << S.g) - 1)) >> b.log_trees) == (b.first >> b.log_trees);
                padded += if same_tree { p.length } else { 0 };
            }
            if (padded >> (S.parts[0] - S.g + b.log_trees)) != 0 {
                return true;
            }
        }
    }
    false
}

/// Whether the public inputs are well-formed and consistent: `None`, or the fault in words
/// (`lkp_fault`, lkp.h:300-380).
pub fn lkp_fault(S: &LkpPublic) -> Option<&'static str> {
    if S.read_from.is_empty() {
        return Some("LKP: it is not said from which oracle messages keys and multiplicities are read");
    }
    if S.parts.is_empty() {
        return Some("LKP: no part of keys");
    }
    if !(S.mu >= 1 && S.mu <= 6 && S.live < (1u32 << S.mu) && S.planes() >= 2) {
        return Some("LKP: the plane slots are not 2, 4, .. or 64, or fewer than two of them are live, or as many as there are or more (all: 0)");
    }
    // of all parts; below 2^planes <= 2^63 at every step, so the sum cannot wrap
    let mut keys = 0u64;
    if !(S.planes() < 64) {
        return Some("LKP: the sum of all multiplicities could wrap around in the field");
    }
    for &x in &S.parts {
        if !(x >= 1 && x < S.planes() && keys + (1u64 << x) < 1u64 << S.planes()) {
            return Some("LKP: no key in a part, or the multiplicities have too few bits for the number of keys");
        }
        keys += 1u64 << x;
    }
    if !(S.d < F_BITS && S.d + S.planes() < F_BITS) {
        return Some("LKP: the sum of all multiplicities could wrap around in the field");
    }
    if S.parts.len() > 1 && !(S.g == 0 && !S.shifted) {
        return Some("LKP: keys in several parts are served for one function and without trees' numbers only");
    }
    if !(S.g <= S.parts[0]) {
        return Some("LKP: a tree's number has more bits than a key's");
    }
    // tree numbers and key blocks are used with one part only
    let v = S.parts[0];
    let mut least = v; // the smallest v_i
    for &x in &S.parts {
        least = core::cmp::min(least, x);
    }
    // Aligned blocks whose sizes are powers of two: two overlap only if one contains the other;
    // blocks that do not overlap and whose sizes add up to the whole tile it.
    let meet = |a: u64, a_bits: u32, b: u64, b_bits: u32| {
        let bits = core::cmp::max(a_bits, b_bits);
        (a >> bits) == (b >> bits)
    };
    let mut trees = 0u64;
    let mut rows = 0u64;
    for i in 0..S.keys.len() {
        let b = &S.keys[i];
        if !(b.log_trees <= S.g
            && (b.first >> b.log_trees << b.log_trees) == b.first
            && (b.first >> S.g) == 0)
        {
            return Some("LKP: a function's trees are no aligned block of tree numbers");
        }
        for j in 0..i {
            // lkp.h:324: `if (!(!meet(..)))` — the fault is an overlap (meet true), not a gap.
            if meet(b.first, b.log_trees, S.keys[j].first, S.keys[j].log_trees) {
                return Some("LKP: two blocks of tree numbers overlap");
            }
        }
        trees += 1u64 << b.log_trees;
        if b.function < 0 && (b.padding_row >> S.d) != 0 {
            return Some("LKP: a padding row is no row of the table");
        }
    }
    if trees != 1u64 << S.g {
        return Some("LKP: the blocks do not cover all tree numbers");
    }
    if !S.shifted {
        // unshifted, a key of one function could be found in another's table
        for b in &S.keys {
            if !(b.function <= 0) {
                return Some("LKP: several functions share a table without the shift");
            }
        }
        for t in &S.tables {
            if !(t.function == 0) {
                return Some("LKP: several functions share a table without the shift");
            }
        }
    }
    if !(S.h <= S.d) {
        return Some("LKP: a table part's number has more bits than a row's");
    }
    for i in 0..S.tables.len() {
        let t = &S.tables[i];
        if S.h != 0 {
            // one part for each number, in the order of the numbers
            if !(t.first == i as u64 && t.log_rows <= S.d - S.h) {
                return Some("LKP: the table parts are not numbered 0, 1, .., or a part's table has more rows than a part");
            }
            if !(t.rows.is_empty() || t.rows.len() == 1usize << t.log_rows) {
                return Some("LKP: a written-out table has not the announced number of rows");
            }
            rows += 1u64 << (S.d - S.h);
            continue;
        }
        if !(t.log_rows <= S.d
            && (t.first >> t.log_rows << t.log_rows) == t.first
            && (t.first >> S.d) == 0)
        {
            return Some("LKP: a table is no aligned block of the rows");
        }
        if !(t.rows.is_empty() || t.rows.len() == 1usize << t.log_rows) {
            return Some("LKP: a written-out table has not the announced number of rows");
        }
        for j in 0..i {
            // lkp.h:344: `if (!(!meet(..)))` — the fault is an overlap (meet true), not a gap.
            if meet(t.first, t.log_rows, S.tables[j].first, S.tables[j].log_rows) {
                return Some("LKP: two tables overlap in the rows");
            }
        }
        rows += 1u64 << t.log_rows;
    }
    if rows != 1u64 << S.d {
        return Some("LKP: the tables do not cover all rows");
    }
    if S.padding.len() > 4096 {
        return Some("LKP: more than 4096 runs of padding");
    }
    for i in 0..S.padding.len() {
        let p = &S.padding[i];
        if p.part as usize >= S.parts.len() {
            return Some("LKP: a run of padding lies in a part that is not there");
        }
        let bits = S.parts[p.part as usize];
        if p.length < 1
            || p.log_step >= bits
            || (p.first >> bits) != 0
            || p.length > 1u64 << (bits - p.log_step)
            || ((p.first + ((p.length - 1) << p.log_step)) >> bits) != 0
        {
            return Some("LKP: a run of padding is empty or does not lie in its part");
        }
        if (p.row >> S.d) != 0 {
            return Some("LKP: a padding row is no row of the table");
        }
        if S.g != 0 && p.log_step < S.g {
            return Some("LKP: a run of padding leaves its tree");
        }
        for b in &S.keys {
            if ((p.first & ((1u64 << S.g) - 1)) >> b.log_trees) == (b.first >> b.log_trees)
                && b.function < 0
            {
                return Some("LKP: a run of padding lies in a tree of padding alone");
            }
        }
        if i != 0
            && !(S.padding[i - 1].part < p.part
                || (S.padding[i - 1].part == p.part && S.padding[i - 1].first < p.first))
        {
            return Some("LKP: the runs of padding are not in increasing order");
        }
        for j in 0..i {
            // two runs with steps that are powers of two
            let (fine, coarse) = if S.padding[j].log_step <= p.log_step {
                (&S.padding[j], p)
            } else {
                (p, &S.padding[j])
            };
            if fine.part != coarse.part
                || (((fine.first ^ coarse.first) & ((1u64 << fine.log_step) - 1)) != 0)
            {
                continue; // another part, or another residue modulo the finer step
            }
            let low = fine.first;
            let high = fine.first + ((fine.length - 1) << fine.log_step);
            // index in the coarse run of its first key number >= low
            let skip = if coarse.first >= low {
                0
            } else {
                (low - coarse.first + (1u64 << coarse.log_step) - 1) >> coarse.log_step
            };
            if skip < coarse.length && coarse.first + (skip << coarse.log_step) <= high {
                return Some("LKP: two runs of padding meet");
            }
        }
    }
    // A padding entry is not read: if every entry of the lookup, of a part or of a function's trees
    // were padding, an accepted proof would say nothing about what was sent there.
    if lkp_only_padding(S) {
        return Some("LKP: no key is left that is no padding: in the look-up, in a part, or in a function's trees");
    }
    if !S.last_key_level_order.is_empty() {
        let mut seen = vec![false; (least - 1) as usize];
        for &j in &S.last_key_level_order {
            if !(j < least - 1 && !seen[j as usize]) {
                return Some("LKP: the last key level's order names a variable twice, or one that a part has not");
            }
            seen[j as usize] = true;
        }
    }
    None
}

/// `lkp_public_check` (lkp.h:388-392): `lkp_fault`, and the check that needs the statement.
pub fn lkp_public_check(st: &Statement, S: &LkpPublic) {
    assert!(lkp_fault(S).is_none(), "{}", lkp_fault(S).unwrap());
    for &o in &S.read_from {
        assert!(
            st.oracle(o).sampled,
            "LKP: an oracle message that keys or multiplicities are read from has no answered sample"
        );
    }
}

/// The key block whose trees include this key number's tree (`lkp_block_of`, lkp.h:395-401).
pub fn lkp_block_of(S: &LkpPublic, key_number: u64) -> &LkpKeyBlock {
    let y = key_number & ((1u64 << S.g) - 1);
    for b in &S.keys {
        if (y >> b.log_trees) == (b.first >> b.log_trees) {
            return b;
        }
    }
    panic!("LKP: a tree number that belongs to no block");
}

/// The number of a key block in `S.keys` (`&lkp_block_of(..) - S.keys.data()`, lkp.h:867).
fn lkp_block_index(S: &LkpPublic, key_number: u64) -> usize {
    let y = key_number & ((1u64 << S.g) - 1);
    for (i, b) in S.keys.iter().enumerate() {
        if (y >> b.log_trees) == (b.first >> b.log_trees) {
            return i;
        }
    }
    panic!("LKP: a tree number that belongs to no block");
}

/// Row `t` of the table, after the shift (`lkp_row`, lkp.h:403-411).
pub fn lkp_row(S: &LkpPublic, theta: E, t: u64) -> E {
    for p in &S.tables {
        if if S.h != 0 {
            (t & ((1u64 << S.h) - 1)) != p.first
        } else {
            (t >> p.log_rows) != (p.first >> p.log_rows)
        } {
            continue;
        }
        // the table's own row; with h > 0 the table is repeated
        let own = (if S.h != 0 { t >> S.h } else { t }) & ((1u64 << p.log_rows) - 1);
        return (if p.rows.is_empty() {
            E::from_base(F::from_u64(own))
        } else {
            p.rows[own as usize]
        }) + E::from_base(F::from_u64(p.function as u64)) * theta;
    }
    panic!("LKP: a row that belongs to no part of the table");
}

/// Whether key number `i` of a part is in a run of `LkpPublic::padding` (`lkp_is_padding`,
/// lkp.h:413-417); key blocks are not looked at.
pub fn lkp_is_padding(S: &LkpPublic, part: u32, i: u64) -> bool {
    for p in &S.padding {
        if p.part == part
            && i >= p.first
            && ((i - p.first) & ((1u64 << p.log_step) - 1)) == 0
            && ((i - p.first) >> p.log_step) < p.length
        {
            return true;
        }
    }
    false
}

/// The number of all padding entries, in runs and in key blocks (`lkp_padding_count`,
/// lkp.h:419-425).
pub fn lkp_padding_count(S: &LkpPublic) -> u64 {
    let mut n = 0u64;
    for p in &S.padding {
        n += p.length;
    }
    for b in &S.keys {
        if b.function < 0 {
            n += 1u64 << (S.parts[0] - S.g + b.log_trees);
        }
    }
    n
}

// ---- cubes (lkp.h:426-460) ----

/// The key numbers `i` of a part with `(i & mask) == value` (`LkpCube`, lkp.h:427-429).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LkpCube {
    pub mask: u64,
    pub value: u64,
}

/// A run as disjoint cubes: at most two for each bit of a key number (`lkp_cubes`,
/// lkp.h:431-441).
pub fn lkp_cubes(p: &LkpPadding, bits: u32) -> Vec<LkpCube> {
    let mut cubes = Vec::new();
    let all = (1u64 << bits) - 1;
    let low = (1u64 << p.log_step) - 1;
    let mut x = p.first >> p.log_step;
    let mut left = p.length;
    while left != 0 {
        let mut b = 0u32; // the largest aligned block that begins at x and fits
        while b < 62 && (x & ((2u64 << b) - 1)) == 0 && (2u64 << b) <= left {
            b += 1;
        }
        cubes.push(LkpCube {
            mask: all & !(((1u64 << b) - 1) << p.log_step),
            value: (p.first & low) | (x << p.log_step),
        });
        x += 1u64 << b;
        left -= 1u64 << b;
    }
    cubes
}

/// The trees of a key block as a cube (`lkp_cube`, lkp.h:443).
pub fn lkp_cube(S: &LkpPublic, b: &LkpKeyBlock) -> LkpCube {
    LkpCube {
        mask: ((1u64 << S.g) - 1) & !((1u64 << b.log_trees) - 1),
        value: b.first,
    }
}

/// The sum of `eq(z, i)` over a cube (`lkp_cube_weight`, lkp.h:446-451).
pub fn lkp_cube_weight(c: &LkpCube, z: &[E]) -> E {
    let mut w = E::one();
    for t in 0..z.len() {
        if ((c.mask >> t) & 1) != 0 {
            w = w * (if ((c.value >> t) & 1) != 0 { z[t] } else { E::one() - z[t] });
        }
    }
    w
}

/// `scalar * eq(z, .)` on the cube, 0 elsewhere, as a product form (`lkp_cube_tensor`,
/// lkp.h:452-460).
pub fn lkp_cube_tensor(c: &LkpCube, z: &[E], scalar: E) -> Tensor {
    let mut v = Tensor::default();
    v.scalar = scalar;
    for t in 0..z.len() {
        let picked = ((c.mask >> t) & 1) != 0;
        let one = ((c.value >> t) & 1) != 0;
        v.push(
            if picked && one { E::zero() } else { E::one() - z[t] },
            if picked && !one { E::zero() } else { z[t] },
        );
    }
    v
}

// ---- the table (lkp.h:461-505) ----

/// All rows of the table, after the shift (`lkp_rows`, lkp.h:462-470).
pub fn lkp_rows(S: &LkpPublic, theta: E) -> Vec<E> {
    let mut rows = vec![E::zero(); 1usize << S.d];
    for t in &S.tables {
        for i in 0..(1u64 << (if S.h != 0 { S.d - S.h } else { t.log_rows })) {
            // the table's own row; with h > 0 the table is repeated
            let own = i & ((1u64 << t.log_rows) - 1);
            rows[(if S.h != 0 { t.first + (i << S.h) } else { t.first + i }) as usize] =
                (if t.rows.is_empty() {
                    E::from_base(F::from_u64(own))
                } else {
                    t.rows[own as usize]
                }) + E::from_base(F::from_u64(t.function as u64)) * theta;
        }
    }
    rows
}

/// The table's multilinear extension at a point (`lkp_table_at`, lkp.h:475-495).
pub fn lkp_table_at(S: &LkpPublic, theta: E, point: &[E]) -> E {
    let mut sum = E::zero();
    for t in &S.tables {
        let mut weight = E::one();
        let mut own = E::zero();
        let (from, to) = if S.h != 0 { (0, S.h) } else { (t.log_rows, S.d) };
        for j in from..to {
            weight = weight
                * (if ((t.first >> j) & 1) != 0 {
                    point[j as usize]
                } else {
                    E::one() - point[j as usize]
                });
        }
        // the coordinates of the table's own row
        let z = &point[S.h as usize..];
        if t.rows.is_empty() {
            let mut two_to = E::one();
            for j in 0..t.log_rows {
                own += two_to * z[j as usize];
                two_to = two_to + two_to;
            }
        } else {
            let mut fold = t.rows.clone();
            for j in 0..t.log_rows {
                for i in 0..fold.len() / 2 {
                    fold[i] = fold[2 * i] + z[j as usize] * (fold[2 * i + 1] - fold[2 * i]);
                }
                fold.truncate(fold.len() / 2);
            }
            own = fold[0];
        }
        sum += weight * (own + E::from_base(F::from_u64(t.function as u64)) * theta);
    }
    sum
}

/// `lkp_shape` (lkp.h:496-505).
pub fn lkp_shape(fixed: &LkpPublic, theta: E) -> LkpShape {
    let mut S = LkpShape {
        d: fixed.d,
        mu: fixed.mu,
        planes: fixed.planes(),
        part_bits: fixed.part_bits().to_vec(),
        all_keys: fixed.all_keys(),
        last_key_level_order: fixed.last_key_level_order.clone(),
        ..LkpShape::default()
    };
    for p in &fixed.padding {
        S.padding.push((p.length, lkp_row(fixed, theta, p.row)));
    }
    for b in &fixed.keys {
        if b.function < 0 {
            S.padding.push((
                1u64 << (S.part_bits[0] - fixed.g + b.log_trees),
                lkp_row(fixed, theta, b.padding_row),
            ));
        }
    }
    let captured = fixed.clone();
    S.table_at = Rc::new(move |point: &[E]| lkp_table_at(&captured, theta, point));
    S
}

// ---- orders (lkp.h:507-547) ----

/// From the highest variable down (`lkp_default_order`, lkp.h:508-512).
pub fn lkp_default_order(variables: u32) -> Vec<u32> {
    let mut order = Vec::new();
    let mut j = variables;
    while j > 0 {
        j -= 1;
        order.push(j);
    }
    order
}

/// The named variables first, the others from the highest down (`lkp_order_beginning`,
/// lkp.h:514-519).
pub fn lkp_order_beginning(first: &[u32], variables: u32) -> Vec<u32> {
    let mut order = first.to_vec();
    let mut j = variables;
    while j > 0 {
        j -= 1;
        if !first.contains(&j) {
            order.push(j);
        }
    }
    order
}

/// An order of rounds for a level whose index has a tree's number in its low g bits
/// (`lkp_range_order`, lkp.h:523-531). Needs at least `g + 9` variables. Only tests call it.
pub fn lkp_range_order(variables: u32, g: u32) -> Vec<u32> {
    assert!(
        variables >= g + 9,
        "LKP: the range order needs nine variables above the tree's number"
    );
    let mut order = Vec::new();
    let mut three = 0u32;
    while three < 9 {
        let mut i = 3u32;
        while i > 0 {
            i -= 1;
            order.push(g + three + i);
        }
        three += 3;
    }
    let mut j = variables;
    while j > g + 9 {
        j -= 1;
        order.push(j);
    }
    let mut j = g;
    while j > 0 {
        j -= 1;
        order.push(j);
    }
    order
}

/// The table with its index bits moved (`lkp_in_order`, lkp.h:533-541): bit j of the new index is
/// bit `order[j]` of the old one.
pub fn lkp_in_order(table: &[E], order: &[u32]) -> Vec<E> {
    let mut moved = vec![E::zero(); table.len()];
    for i in 0..table.len() {
        let mut old = 0usize;
        for j in 0..order.len() {
            old |= ((i >> j) & 1) << order[j];
        }
        moved[i] = table[old];
    }
    moved
}

/// A point given round by round, with each coordinate put back at its variable's place
/// (`lkp_by_variable`, lkp.h:543-547).
pub fn lkp_by_variable(by_round: &[E], order: &[u32]) -> Vec<E> {
    let mut point = vec![E::zero(); by_round.len()];
    for j in 0..order.len() {
        point[order[j] as usize] = by_round[j];
    }
    point
}

/// Steps 3, 4, 5 and 6 of the protocol (`LkpStep`, lkp.h:550).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LkpStep {
    Keys,
    Table,
    Leaves,
    Bits,
}

// ---- the summands (lkp.h:618-658) ----

/// `y_0 y_1`, for steps 1b, 3 and 4 (`lkp_summand_product`, lkp.h:623-628).
pub fn lkp_summand_product() -> Summand {
    Summand {
        shown: 2,
        kept: 0,
        degree: 2,
        at: Box::new(|_p: &[E], y: &[E]| vec![y[0] * y[1]]),
    }
}

/// Step 1, on `(Z, P_1, G_0)` if `first`, else on `(P_(j+1), G_j)` (`lkp_summand_tie`,
/// lkp.h:630-638).
pub fn lkp_summand_tie(first: bool, a: E) -> Summand {
    if first {
        Summand {
            shown: 3,
            kept: 0,
            degree: 3,
            at: Box::new(move |_p: &[E], y: &[E]| vec![y[0] - a * y[1] * y[1] * y[2]]),
        }
    } else {
        Summand {
            shown: 2,
            kept: 0,
            degree: 3,
            at: Box::new(|_p: &[E], y: &[E]| vec![y[0] * y[0] * y[1]]),
        }
    }
}

/// Step 5, affine in the kept map b (`lkp_summand_leaves`, lkp.h:641-651).
pub fn lkp_summand_leaves(S: &LkpShape, alpha: E, order: &[u32]) -> Summand {
    let mu = S.mu;
    let table_at = S.table_at.clone();
    let order = order.to_vec();
    Summand {
        shown: 0,
        kept: 1,
        degree: 0,
        at: Box::new(move |by_round: &[E], _y: &[E]| {
            let point = lkp_by_variable(by_round, &order);
            vec![E::one(), alpha - E::one() - table_at(&point[mu as usize..])]
        }),
    }
}

/// Step 6 (`lkp_summand_bits`, lkp.h:653-658).
pub fn lkp_summand_bits() -> Summand {
    Summand {
        shown: 1,
        kept: 0,
        degree: 2,
        at: Box::new(|_p: &[E], y: &[E]| vec![y[0] * y[0] - y[0]]),
    }
}

/// The number of mask entries that the two inner masks of each part's last key level use
/// (`lkp_key_masks`, lkp.h:667).
pub fn lkp_key_masks(S: &LkpPublic) -> usize {
    2 * S.parts.len()
}

/// The number of mask entries that a lookup uses (`lkp_masks`, lkp.h:668-677).
pub fn lkp_masks(S: &LkpPublic) -> usize {
    let mut n = 7 + 6 * (S.planes() as usize - 2);
    n += 5 * (S.parts.len() - 1);
    for &v in &S.parts {
        for k in 0..v {
            n += 2 * k as usize + 5;
        }
    }
    for l in 0..S.d {
        n += 2 * (S.mu + l) as usize + 5;
    }
    n += 1 + S.mu as usize + 2 * S.d as usize; // the leaves: no round of PSC's variable Y, no end value
    n += 1 + 2 * (S.mu + S.d) as usize + 2 + 1; // the bits
    n
}

// ---- the claims on the keys (lkp.h:573-616) ----

/// What LKP leaves to its caller, one for each part of the keys (`LkpKeys`, lkp.h:579-585):
/// `sum_i weights[i] * key[i] + <masks> = target`.
#[derive(Debug)]
pub struct LkpKeys {
    pub point: Vec<E>,
    /// On the part's key numbers: `eq(point, .)` less one product form per padding cube.
    pub weights: Form,
    pub masks: Vec<MaskTerm<E>>,
    pub target: E,
}

impl Default for LkpKeys {
    fn default() -> Self {
        LkpKeys { point: Vec::new(), weights: Form::default(), masks: Vec::new(), target: E::zero() }
    }
}

/// A lookup's `LkpKeys` (`LkpKeyClaim`, lkp.h:589-610). Every claim must be taken; the destructor
/// panics if one is left and the channel has not rejected the proof. The rejection is reported by
/// `lkp_run`, because `VerifierRounds` keeps its fate private.
pub struct LkpKeyClaim {
    claims: Vec<LkpKeys>,
    full: Vec<bool>,
    left: usize,
    rejected: Rc<Cell<bool>>,
}

impl Default for LkpKeyClaim {
    fn default() -> Self {
        LkpKeyClaim { claims: Vec::new(), full: Vec::new(), left: 0, rejected: Rc::new(Cell::new(false)) }
    }
}

impl LkpKeyClaim {
    pub fn parts(&self) -> usize {
        self.claims.len()
    }
    /// The C++ `put(LkpKeys&&, const Rounds&)`; the channel is reported through `channel_rejected`.
    pub fn put(&mut self, claim: LkpKeys) {
        self.claims.push(claim);
        self.full.push(true);
        self.left += 1;
    }
    pub fn take(&mut self, part: usize) -> LkpKeys {
        assert!(
            part < self.claims.len() && self.full[part],
            "LKP: there is no such claim on a key vector, or it has been taken"
        );
        self.full[part] = false;
        self.left -= 1;
        core::mem::take(&mut self.claims[part])
    }
    /// Whether the channel has rejected the proof (`channel_->ok()` in C++).
    pub fn channel_rejected(&self) {
        self.rejected.set(true);
    }
    pub fn rejected(&self) -> bool {
        self.rejected.get()
    }
}

impl Drop for LkpKeyClaim {
    fn drop(&mut self) {
        assert!(
            self.left == 0 || self.rejected.get(),
            "LKP: the claim on the key vector was dropped: the caller has made no row of it"
        );
    }
}

/// What `lkp_run` fills in for the caller (`LkpOutput`, lkp.h:612-616).
#[derive(Default)]
pub struct LkpOutput {
    pub theta: E,
    pub alpha: E,
    pub keys: LkpKeyClaim,
    /// Copies of the claims that LKP added to the group, for tests and reports.
    pub rows: Vec<Row>,
}

/// The caller's callback that adds a product-form vector on the multiplicities
/// (`LkpPlanesAt`, lkp.h:571). `Rc` models the copyable `std::function`.
pub type LkpPlanesAt = Rc<dyn Fn(&mut Row, Tensor)>;

// ---- the verifier's side (lkp.h:939-960) ----

/// The verifier's side of one lookup (`LkpVerifierSide`, lkp.h:939-960).
pub struct LkpVerifierSide<'v, 'x, 'a, 'd, 's> {
    pub V: &'v mut VerifierContext<'x, 'a, 'd, 's>,
    pub masks: OracleId,
    pub key_masks: OracleId,
}

impl<'v, 'x, 'a, 'd, 's> LkpVerifierSide<'v, 'x, 'a, 'd, 's> {
    pub fn ch(&mut self) -> &mut VerifierRounds<'a, 'd, 's> {
        &mut *self.V.ch
    }
    pub fn statement(&mut self) -> &mut Statement {
        &mut self.V.st
    }
    pub fn note(&mut self, what: &str, value: E) {
        self.V.note(what, value);
    }
    /// One PSC of the tie (`LkpVerifierSide::tie`, lkp.h:948-951).
    pub fn tie(
        &mut self,
        claim: SumClaim,
        s: &Summand,
        _j: usize,
        out: &mut PscOutput,
        calls: &mut HashCalls,
    ) -> bool {
        let fresh = lkp_fresh(
            &mut self.V.st,
            self.masks,
            self.key_masks,
            psc_masks(&claim, s),
            false,
        );
        psc_verify(&mut *self.V.ch, claim, s, fresh, out, calls)
    }
    /// One PSC of step 1b (`LkpVerifierSide::split`, lkp.h:952-955).
    pub fn split(
        &mut self,
        claim: SumClaim,
        s: &Summand,
        _i: usize,
        out: &mut PscOutput,
        calls: &mut HashCalls,
    ) -> bool {
        let fresh = lkp_fresh(
            &mut self.V.st,
            self.masks,
            self.key_masks,
            psc_masks(&claim, s),
            false,
        );
        psc_verify(&mut *self.V.ch, claim, s, fresh, out, calls)
    }
    /// One PSC of steps 3 to 6 (`LkpVerifierSide::psc`, lkp.h:956-959).
    #[allow(clippy::too_many_arguments)]
    pub fn psc(
        &mut self,
        claim: SumClaim,
        s: &Summand,
        _step: LkpStep,
        _part: u32,
        _level: u32,
        _order: &[u32],
        last_of_keys: bool,
        out: &mut PscOutput,
        calls: &mut HashCalls,
    ) -> bool {
        let fresh = lkp_fresh(
            &mut self.V.st,
            self.masks,
            self.key_masks,
            psc_masks(&claim, s),
            last_of_keys,
        );
        psc_verify(&mut *self.V.ch, claim, s, fresh, out, calls)
    }
}

/// The n mask entries of one PSC (`lkp_fresh`, lkp.h:881-886). The C++ takes two ledgers; the
/// port takes the statement and the two oracle numbers, and handles `masks == key_masks`.
pub fn lkp_fresh(
    st: &mut Statement,
    masks: OracleId,
    key_masks: OracleId,
    n: usize,
    keys: bool,
) -> Vec<MaskSlot> {
    if !keys {
        return st.masks(masks).take_n(n);
    }
    assert!(n >= 2, "LKP: a PSC with two inner mask entries has fewer than two entries");
    let mut fresh = st.masks(masks).take_n(n - 2);
    let inner = st.masks(key_masks).take_n(2);
    fresh.extend(inner);
    fresh
}

fn empty_point_claim() -> PointClaim {
    PointClaim { point: Vec::new(), masks: Vec::new(), value: E::zero() }
}

fn empty_sum_claim() -> SumClaim {
    SumClaim { vars: Vec::new(), masks: Vec::new(), target: E::zero() }
}

fn empty_psc_output() -> PscOutput {
    PscOutput {
        point: Vec::new(),
        row_masks: Vec::new(),
        row_maps: Vec::new(),
        row_target: E::zero(),
        ends: Vec::new(),
    }
}

/// Adds LKP's row to the group, after checking that every main-table entry that it reads is
/// declared (`leave` in lkp_run, lkp.h:714-724).
fn lkp_leave(
    side: &mut LkpVerifierSide<'_, '_, '_, '_, '_>,
    fixed: &LkpPublic,
    group: GroupId,
    rows: &mut Vec<Row>,
    row: Row,
) {
    let declared = |o: OracleId| fixed.read_from.contains(&o);
    let mut all = true;
    for t in &row.terms {
        all = all && (t.part != Part::Main || declared(t.oracle));
    }
    for u in &row.units {
        all = all && (u.part != Part::Main || declared(u.oracle));
    }
    for r in &row.runs {
        all = all && (r.part != Part::Main || declared(r.oracle));
    }
    for f in &row.forms {
        all = all && declared(f.oracle);
    }
    assert!(
        all,
        "LKP: a row reads the main table of an oracle message that is not among those declared as read"
    );
    rows.push(row.clone());
    side.V.st.add_row(group, row);
}

/// Steps 3 and 4 (`lkp_level_chain`, lkp.h:686-707): takes `claim` from a tree's top level down to
/// its leaves. Level l has `more + l` variables.
#[allow(clippy::too_many_arguments)]
pub fn lkp_level_chain(
    side: &mut LkpVerifierSide<'_, '_, '_, '_, '_>,
    step: LkpStep,
    part: u32,
    levels: u32,
    more: u32,
    S: &LkpShape,
    claim: &mut PointClaim,
    fixed: &LkpPublic,
    group: GroupId,
    rows: &mut Vec<Row>,
    calls: &mut HashCalls,
) -> bool {
    let name = if step == LkpStep::Table {
        String::from("LKP table, level ")
    } else if S.part_bits.len() > 1 {
        format!("LKP keys, part {}, level ", part)
    } else {
        String::from("LKP keys, level ")
    };
    let product = lkp_summand_product();
    for l in 0..levels {
        let variables = more + l;
        let mut order = lkp_default_order(variables);
        let last_of_keys = step == LkpStep::Keys && l + 1 == levels;
        if last_of_keys {
            order = lkp_order_beginning(&S.last_key_level_order, variables);
        }
        assert!(
            order.len() == variables as usize && claim.point.len() == variables as usize,
            "LKP: a level's order or point has not one entry for each variable"
        );
        let mut sum = empty_sum_claim();
        for j in 0..variables {
            sum.vars.push(Weight::equality(claim.point[order[j as usize] as usize], 3));
        }
        sum.masks = core::mem::take(&mut claim.masks);
        sum.target = claim.value;
        let mut out = empty_psc_output();
        if !side.psc(sum, &product, step, part, l, &order, last_of_keys, &mut out, calls) {
            return false;
        }
        let row = psc_row_u(&mut out, &[], format!("{}{}", name, l));
        lkp_leave(side, fixed, group, rows, row);
        for e in &mut out.ends {
            e.point = lkp_by_variable(&e.point, &order);
        }
        let mut ends = core::mem::take(&mut out.ends).into_iter();
        let half0 = ends.next().unwrap();
        let half1 = ends.next().unwrap();
        *claim = line(&mut *side.V.ch, half0, half1, calls);
    }
    true
}

/// The C++ block at the end of `lkp_run` that turns a part's claim on its leaves into a claim on
/// the real keys before the shift (lkp.h:842-874). Extracted so that the vector tool and the test
/// can compare it without a channel.
pub fn lkp_key_claim(
    fixed: &LkpPublic,
    theta: E,
    alpha: E,
    part: usize,
    on_leaves: PointClaim,
) -> LkpKeys {
    let PointClaim { point, masks, value } = on_leaves;
    let mut k = LkpKeys { point, weights: Form::default(), masks: Vec::new(), target: alpha - value };
    for m in masks {
        k.masks.push(MaskTerm { slot: m.slot, coeff: -m.coeff });
    }
    k.weights.add(Tensor::eq(&k.point, k.point.len() as u32, E::one()));
    // a cube of padding entries holding `row`
    let take_out = |k: &mut LkpKeys, cube: &LkpCube, row: u64| -> E {
        let weight = lkp_cube_weight(cube, &k.point);
        k.target = k.target - weight * lkp_row(fixed, theta, row);
        k.weights.add(lkp_cube_tensor(cube, &k.point, -E::one()));
        weight
    };
    let mut real = vec![E::zero(); fixed.keys.len()]; // the weight of each key block's real keys
    for b in 0..fixed.keys.len() {
        if fixed.keys[b].function < 0 {
            let cube = lkp_cube(fixed, &fixed.keys[b]);
            take_out(&mut k, &cube, fixed.keys[b].padding_row);
        } else {
            real[b] = lkp_cube_weight(&lkp_cube(fixed, &fixed.keys[b]), &k.point);
        }
    }
    for p in &fixed.padding {
        if p.part as usize != part {
            continue;
        }
        let b = lkp_block_index(fixed, p.first);
        for cube in lkp_cubes(p, k.point.len() as u32) {
            real[b] = real[b] - take_out(&mut k, &cube, p.row);
        }
    }
    for b in 0..fixed.keys.len() {
        if fixed.keys[b].function > 0 {
            k.target = k.target
                - theta
                    * E::from_base(F::from_u64(fixed.keys[b].function as u64))
                    * real[b];
        }
    }
    k
}

/// The whole protocol, the verifier's side (`lkp_run`, lkp.h:711-876). False: the channel has
/// rejected the proof. True alone decides nothing; the claims in `out` are still to be tested.
pub fn lkp_run(
    side: &mut LkpVerifierSide<'_, '_, '_, '_, '_>,
    fixed: &LkpPublic,
    planes: &LkpPlanesAt,
    group: GroupId,
    out: &mut LkpOutput,
    calls: &mut HashCalls,
) -> bool {
    lkp_public_check(&side.V.st, fixed);
    // Every linear claim of LKP's own goes into the group here, so that no caller can lose one.
    // (The `leave` closure of C++ is `lkp_leave`, called at each site.)

    out.theta = if fixed.shifted {
        let mut draw = side.V.ch.close_algebraic(R_LKP_SHIFT, calls);
        draw.draw(calls)
    } else {
        E::zero()
    };
    let S = lkp_shape(fixed, out.theta);
    let w = 1usize << S.mu;
    let alpha = {
        let mut draw = side.V.ch.close_algebraic(R_LKP, calls);
        draw.draw(calls)
    };
    out.alpha = alpha;
    let mut a = E::one();
    let mut padding = 0u64;
    for &(count, value) in &S.padding {
        let mut power = alpha - value; // (alpha - value)^count by squaring
        let mut e = count;
        while e != 0 {
            if e & 1 != 0 {
                a = a * power;
            }
            e >>= 1;
            power = power * power;
        }
        padding += count;
    }
    assert!(
        padding == lkp_padding_count(fixed),
        "LKP: the padding's factor and its count differ"
    );
    side.note("LKP: alpha", alpha);
    side.note("LKP: the public factor a", a);

    // 1: the tie
    let mut on_root = empty_point_claim();
    let mut on_power = empty_point_claim();
    let mut on_plane: Vec<PointClaim> = Vec::new();
    for j in 0..(S.planes - 1) as usize {
        let mut sum = empty_sum_claim();
        sum.target = E::zero();
        if j != 0 {
            sum = SumClaim::at_point(core::mem::replace(&mut on_power, empty_point_claim()), &[]);
        }
        let mut step = empty_psc_output();
        if !side.tie(sum, &lkp_summand_tie(j == 0, a), j, &mut step, calls) {
            out.keys.channel_rejected();
            return false;
        }
        let row = psc_row_u(&mut step, &[], format!("LKP tie, step {}", j));
        lkp_leave(side, fixed, group, &mut out.rows, row);
        let mut ends = core::mem::take(&mut step.ends).into_iter();
        if j == 0 {
            on_root = ends.next().unwrap();
        }
        on_power = ends.next().unwrap();
        on_plane.push(ends.next().unwrap());
    }
    on_plane.push(on_power); // the last power is the last live plane's root

    // 1b: from the product of the parts' roots to each root
    let mut on_roots: Vec<PointClaim> = Vec::new();
    for i in 0..S.part_bits.len() - 1 {
        let mut step = empty_psc_output();
        if !side.split(
            SumClaim::at_point(core::mem::replace(&mut on_root, empty_point_claim()), &[]),
            &lkp_summand_product(),
            i,
            &mut step,
            calls,
        ) {
            out.keys.channel_rejected();
            return false;
        }
        let row = psc_row_u(&mut step, &[], format!("LKP parts, step {}", i));
        lkp_leave(side, fixed, group, &mut out.rows, row);
        let mut ends = core::mem::take(&mut step.ends).into_iter();
        on_roots.push(ends.next().unwrap());
        on_root = ends.next().unwrap();
    }
    on_roots.push(on_root);

    // 2: one claim on the table side's top level
    let mut on_table = empty_point_claim();
    {
        let mut from = side.V.ch.close_algebraic(R_LKP_PLANES, calls);
        for _ in 0..S.mu {
            on_table.point.push(from.draw(calls));
        }
    }
    on_table.value = E::zero();
    for j in 0..w {
        let mut weight = E::one();
        for t in 0..S.mu {
            weight = weight
                * (if ((j >> t) & 1) != 0 {
                    on_table.point[t as usize]
                } else {
                    E::one() - on_table.point[t as usize]
                });
        }
        if j >= S.planes as usize {
            // a slot of public zeros: its leaves are 1, and so is its root
            on_table.value += weight;
            continue;
        }
        let masks = core::mem::take(&mut on_plane[j].masks);
        for m in masks {
            on_table.masks.push(MaskTerm { slot: m.slot, coeff: weight * m.coeff });
        }
        on_table.value += weight * on_plane[j].value;
    }
    side.note("LKP: the table side's first claim", on_table.value);

    // 3, 4: the trees of the key side and of the table side
    for part in 0..S.part_bits.len() {
        if !lkp_level_chain(
            side,
            LkpStep::Keys,
            part as u32,
            S.part_bits[part],
            0,
            &S,
            &mut on_roots[part],
            fixed,
            group,
            &mut out.rows,
            calls,
        ) {
            out.keys.channel_rejected();
            return false;
        }
    }
    if !lkp_level_chain(
        side,
        LkpStep::Table,
        0,
        S.d,
        S.mu,
        &S,
        &mut on_table,
        fixed,
        group,
        &mut out.rows,
        calls,
    ) {
        out.keys.channel_rejected();
        return false;
    }

    // 5: the leaves of the table side
    let all = S.mu + S.d;
    let order = lkp_default_order(all);
    let planes_for_bits = planes.clone();
    let bits_at: MapAt = Box::new(move |row: &mut Row, point: &[E], coeff: E| {
        planes_for_bits(row, Tensor::eq(point, point.len() as u32, coeff));
    });
    {
        let mut sum = empty_sum_claim();
        for j in 0..all {
            sum.vars.push(Weight::equality(
                on_table.point[order[j as usize] as usize],
                if order[j as usize] < S.mu { 2 } else { 3 },
            ));
        }
        sum.masks = core::mem::take(&mut on_table.masks);
        sum.target = on_table.value;
        let mut leaves = empty_psc_output();
        if !side.psc(
            sum,
            &lkp_summand_leaves(&S, alpha, &order),
            LkpStep::Leaves,
            0,
            0,
            &order,
            false,
            &mut leaves,
            calls,
        ) {
            out.keys.channel_rejected();
            return false;
        }
        leaves.point = lkp_by_variable(&leaves.point, &order);
        side.note(
            "LKP: the leaves' factor",
            alpha - E::one() - (S.table_at)(&leaves.point[S.mu as usize..]),
        );
        let row = psc_row_u(&mut leaves, core::slice::from_ref(&bits_at), "LKP leaves");
        lkp_leave(side, fixed, group, &mut out.rows, row);
    }

    // 6: the bits are bits
    {
        let mut point = vec![E::zero(); all as usize];
        {
            let mut from = side.V.ch.close_algebraic(R_ZERO, calls);
            for x in &mut point {
                *x = from.draw(calls);
            }
        }
        let mut sum = empty_sum_claim();
        for j in 0..all {
            sum.vars.push(Weight::equality(point[order[j as usize] as usize], 3));
        }
        sum.target = E::zero();
        let mut bits = empty_psc_output();
        if !side.psc(
            sum,
            &lkp_summand_bits(),
            LkpStep::Bits,
            0,
            0,
            &order,
            false,
            &mut bits,
            calls,
        ) {
            out.keys.channel_rejected();
            return false;
        }
        let row = psc_row_u(&mut bits, &[], "LKP bits");
        lkp_leave(side, fixed, group, &mut out.rows, row);
        let mut end = core::mem::take(&mut bits.ends).into_iter().next().unwrap();
        end.point = lkp_by_variable(&end.point, &order);
        let row = point_row(end, &bits_at, "LKP bits at the point");
        lkp_leave(side, fixed, group, &mut out.rows, row);
    }

    // 7: the multiplicities sum to the number of keys that are not padding
    {
        let mut sum = Row::plain("LKP number of keys");
        let mut v = Tensor::default();
        let mut two_to = E::one() + E::one(); // 2^(2^t)
        for _ in 0..S.mu {
            v.push(E::one(), two_to);
            two_to = two_to * two_to;
        }
        for _ in 0..S.d {
            v.push(E::one(), E::one());
        }
        (planes)(&mut sum, v);
        sum.target = E::from_base(F::from_u64(S.all_keys - padding));
        lkp_leave(side, fixed, group, &mut out.rows, sum);
    }

    // Turns each part's claim on its leaves, alpha - (shifted key, or padding row), into a claim on
    // the real keys before the shift (LkpKeys).
    for (part, on_leaves) in core::mem::take(&mut on_roots).into_iter().enumerate() {
        let k = lkp_key_claim(fixed, out.theta, alpha, part, on_leaves);
        side.note("LKP: a part's key claim", k.target);
        out.keys.put(k);
    }
    true
}

// ---- the entry points (lkp.h:962-989) ----

/// Both mask messages must be fixed before the first challenge under which one of their entries
/// masks a value (`lkp_mask_messages_check`, lkp.h:972-974).
pub fn lkp_mask_messages_check(st: &Statement, masks: OracleId, key_masks: OracleId) {
    assert!(
        st.oracle(masks).sampled && (key_masks == NONE_ID || st.oracle(key_masks).sampled),
        "LKP: an oracle message that gives mask entries has no answered sample"
    );
}

/// All of LKP, the verifier's side (`lkp_verify`, lkp.h:984-989).
#[allow(clippy::too_many_arguments)]
pub fn lkp_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    fixed: &Public<LkpPublic>,
    planes: &LkpPlanesAt,
    masks: OracleId,
    group: GroupId,
    out: &mut LkpOutput,
    key_masks: OracleId,
    calls: &mut HashCalls,
) -> bool {
    lkp_mask_messages_check(&V.st, masks, key_masks);
    let value = V.ch.get(fixed);
    // `V.st.masks(key_masks == NONE_ID ? masks : key_masks)` (lkp.h:985).
    let key_masks = if key_masks == NONE_ID { masks } else { key_masks };
    let mut side = LkpVerifierSide { V, masks, key_masks };
    let ran = lkp_run(&mut side, value, planes, group, out, calls);
    let ok = side.V.ch.ok();
    if !ok {
        out.keys.channel_rejected();
    }
    ran && ok
}

// ---- the multiplicities (lkp.h:1061-1088) ----

/// Writes the honest multiplicities to `bits`, in the layout of the prover's engine
/// (`lkp_count`, lkp.h:1066-1088). Returns false if a counted key is in no row of its function's
/// table. `left_out` empty means none.
pub fn lkp_count(S: &LkpPublic, keys: &[E], bits: &mut Vec<E>, left_out: &[bool]) -> bool {
    let mut count = vec![0u64; 1usize << S.d];
    let mut all = true;
    let mut part = 0usize;
    let mut part_first = 0u64;
    for i in 0..keys.len() {
        let i = i as u64;
        while i - part_first >= 1u64 << S.parts[part] {
            part_first += 1u64 << S.parts[part];
            part += 1;
        }
        let own = i - part_first;
        let function = lkp_block_of(S, own).function;
        if function < 0
            || lkp_is_padding(S, part as u32, own)
            || (!left_out.is_empty() && left_out[i as usize])
        {
            continue;
        }
        let mut found = false;
        for t in &S.tables {
            if t.function as i32 != function {
                continue;
            }
            let mut r = 0u64;
            while r < (1u64 << t.log_rows) && !found {
                let row = if t.rows.is_empty() {
                    E::from_base(F::from_u64(r))
                } else {
                    t.rows[r as usize]
                };
                if row == keys[i as usize] {
                    count[(if S.h != 0 { t.first + (r << S.h) } else { t.first + r }) as usize] += 1;
                    found = true;
                }
                r += 1;
            }
        }
        all = all && found;
    }
    bits.clear();
    bits.resize(count.len() << S.mu, E::zero());
    for t in 0..count.len() {
        for j in 0..(1usize << S.mu) {
            if ((count[t] >> j) & 1) != 0 {
                bits[j + (t << S.mu)] = E::one();
            }
        }
    }
    all
}

// ---- the live planes (lkp.h:1090-1116) ----

/// The live planes `0 .. live - 1` as aligned blocks of plane numbers, the largest first
/// (`lkp_live_blocks`, lkp.h:1092-1101): `(first plane, log2 of the number of planes)`.
pub fn lkp_live_blocks(live: u32) -> Vec<(u32, u32)> {
    let mut blocks = Vec::new();
    let mut first = 0u32;
    while first < live {
        let mut bits = 0u32;
        while first + (2u32 << bits) <= live && (first & ((2u32 << bits) - 1)) == 0 {
            bits += 1;
        }
        blocks.push((first, bits));
        first += 1u32 << bits;
    }
    blocks
}

/// Restricts a product-form vector v to one such block (`lkp_on_block`, lkp.h:1105-1116).
pub fn lkp_on_block(v: &Tensor, mu: u32, block: (u32, u32)) -> Tensor {
    assert!(!v.has_dense(), "LKP: a vector on the multiplicities is a product form");
    let mut part = Tensor::default();
    part.scalar = v.scalar;
    for t in 0..v.vars() {
        if t >= block.1 && t < mu {
            part.scalar = part.scalar
                * (if ((block.0 >> t) & 1) != 0 { v.hi(t) } else { v.lo(t) });
        } else {
            part.push(v.lo(t), v.hi(t));
        }
    }
    part
}

/// `LkpKeys::weights` restricted to one function's own key vector (`lkp_weights_of_block`,
/// lkp.h:1121-1138).
pub fn lkp_weights_of_block(S: &LkpPublic, weights: &Form, block: usize) -> Form {
    assert!(
        block < S.keys.len() && S.keys[block].function >= 0 && weights.entries.is_empty(),
        "LKP: no such function's block, or weights that LKP has not made"
    );
    let b = &S.keys[block];
    let mut own = Form::default();
    for v in &weights.tensors {
        assert!(
            !v.has_dense() && v.vars() == S.parts[0],
            "LKP: weights that LKP has not made"
        );
        let mut part = Tensor::default();
        part.scalar = v.scalar;
        for t in 0..v.vars() {
            if t >= b.log_trees && t < S.g {
                part.scalar = part.scalar
                    * (if ((b.first >> t) & 1) != 0 { v.hi(t) } else { v.lo(t) });
            } else {
                part.push(v.lo(t), v.hi(t));
            }
        }
        own.add(part);
    }
    own
}
