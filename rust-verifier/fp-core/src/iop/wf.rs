//! WF, the verifier's side, ported from `blocks/iop/wf.h` (lines 40-407 and 452-606). The
//! prover's heavy part (`WfHeavy`, `WfCpu`, `wf_prove`, `wf_rows_prove`) and the plan
//! (`wf_plan`, `blocks/frame/wf_frame.h`) are not ported.
//!
//! WF shows that every entry of a committed matrix M is in range, by lookups (LKP) of keys, each a
//! public linear map of entries of M plus a constant. The keys are never sent. What forms the
//! public parameters: the lookups (`WfLookup`), one oracle message (the multiplicities in bit
//! planes, and mask rows), and the stages of a proximity test (IOPP).
//!
//! The module holds the parameters and what follows from them (`wf_lookups`, `wf_layout`,
//! `wf_planes_at`, `wf_weights_on_rows`), the checks (`wf_fault`, `wf_start_check`) and the
//! verifier's entry points (`wf_rows_verify`, `wf_verify`). `WfPending` differs from C++ in one
//! point: `VerifierRounds` keeps its fate private, so the port cannot hold the channel and ask it
//! at drop. A caller reports a rejected channel through `WfPending::channel_rejected`, as
//! `LkpKeyClaim` does; the drop check then matches `WfPending::~WfPending`.

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::Cell;

use super::batt::{batt_masks, TensorRow};
use super::context::{OracleNotice, VerifierContext};
use super::fold::{fold_mask_notice, FoldMask, FoldShape};
use super::iopp::{iopp_fault, iopp_fold_shape, iopp_verify, IoppChoice, IoppStage};
use super::lin::{LinPublic, LinShape};
use super::lkp::{
    lkp_key_masks, lkp_live_blocks, lkp_masks, lkp_on_block, lkp_verify, LkpKeyBlock, LkpKeys,
    LkpOutput, LkpPadding, LkpPlanesAt, LkpPublic, LkpTablePart,
};
use super::relation::{Codes, GroupId, OracleId, Part, Row, Statement, NONE_ID};
use super::send::{send_verify, AnswersRound};
use super::send_pad::free_mask_entries;
use super::tensor::Tensor;
use crate::chain::public::{derive, element, Public, PublicBytes};
use crate::field::ext::{E, F};
use crate::hash::calls::HashCalls;
use crate::iop::message::Writer;
use crate::numbers::codes::ceil_log2;

/// `F_BITS` (`blocks/field/field.h:23`), the number of bits of the base field.
const F_BITS: u32 = 64;

// ------------------------------------------------------------------------------------------------
// The public parameters
// ------------------------------------------------------------------------------------------------

/// A run of consecutive places of a part (`WfRun`, wf.h:43-48). For digit q of its keys, place
/// `first_place + p`, `p < places`, reads matrix row `first_row + p + q * stride`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WfRun {
    pub first_place: u64,
    pub first_row: u64,
    pub places: u64,
    pub stride: u64,
}

/// A part of a lookup's keys (`WfPart`, wf.h:53-61): `2^log_places` places, each with one key for
/// each of the `2^k_col` columns of M.
#[derive(Clone, Debug, Default)]
pub struct WfPart {
    pub log_places: u32,
    /// By rising places, without overlap; a place in no run is padding.
    pub runs: Vec<WfRun>,
}

impl WfPart {
    /// The covered places, after `wf_fault` without wrap-around (`places`, wf.h:56-60).
    pub fn places(&self) -> u64 {
        let mut n = 0u64;
        for r in &self.runs {
            n += r.places;
        }
        n
    }
}

/// One lookup (`WfLookup`, wf.h:69-77): every key at a covered place is a row of the range table
/// `0 .. 2^d - 1`.
#[derive(Clone, Debug, Default)]
pub struct WfLookup {
    pub name: String,
    pub d: u32,
    pub mu: u32,
    /// Of the `2^mu` plane slots, how many are real (0: all).
    pub live: u32,
    /// One weight for each of a place's rows.
    pub digit_weight: Vec<F>,
    pub offset: F,
    /// What a place of padding holds.
    pub padding_key: F,
    pub parts: Vec<WfPart>,
    /// The variables that a part's last key level binds first (`LkpPublic::last_key_level_order`).
    pub first_bound: Vec<u32>,
}

/// The size of M: `rows` rows of `2^k_col` elements of F (`WfMatrix`, wf.h:83-87).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WfMatrix {
    pub k_col: u32,
    pub rows: u64,
}

impl WfMatrix {
    pub fn k_row(&self) -> u32 {
        ceil_log2(self.rows)
    }
}

/// `wf_matrix_of` (wf.h:88).
pub fn wf_matrix_of(table: &LinShape) -> WfMatrix {
    WfMatrix { k_col: table.k_col(), rows: table.matrix_rows }
}

/// WF's public parameters (`WfPublic`, wf.h:93-99).
#[derive(Clone, Debug)]
pub struct WfPublic {
    pub lookups: Vec<WfLookup>,
    /// The multiplicities and masks.
    pub message: OracleNotice,
    /// The number that the message gets on the channel.
    pub message_id: OracleId,
    pub stages: Vec<IoppStage>,
    pub choice: IoppChoice,
}

impl Default for WfPublic {
    fn default() -> Self {
        WfPublic {
            lookups: Vec::new(),
            message: OracleNotice { shape: Default::default(), leaf_class: 0 },
            message_id: NONE_ID,
            stages: Vec::new(),
            choice: IoppChoice::default(),
        }
    }
}

impl PublicBytes for WfRun {
    /// `public_bytes(Writer&, const WfRun&)` (wf.h:100).
    fn public_bytes(&self, w: &mut Writer) {
        for x in [self.first_place, self.first_row, self.places, self.stride] {
            w.put_u64(x);
        }
    }
    fn public_fault(&self) -> Option<&'static str> {
        wf_run_fault(self)
    }
}

impl PublicBytes for WfPart {
    /// `public_bytes(Writer&, const WfPart&)` (wf.h:101).
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.log_places as u64);
        w.put_u64(self.runs.len() as u64);
        for r in &self.runs {
            r.public_bytes(w);
        }
    }
    fn public_fault(&self) -> Option<&'static str> {
        wf_part_fault(self)
    }
}

impl PublicBytes for WfLookup {
    /// `public_bytes(Writer&, const WfLookup&)` (wf.h:102-105). Not the name: it only labels the
    /// lookup's rounds and messages in the plan (`wf_plan`).
    fn public_bytes(&self, w: &mut Writer) {
        for x in [self.d, self.mu, self.live] {
            w.put_u64(x as u64);
        }
        w.put_u64(self.digit_weight.len() as u64);
        for x in &self.digit_weight {
            w.put_f(*x);
        }
        w.put_f(self.offset);
        w.put_f(self.padding_key);
        w.put_u64(self.parts.len() as u64);
        for p in &self.parts {
            p.public_bytes(w);
        }
        w.put_u64(self.first_bound.len() as u64);
        for x in &self.first_bound {
            w.put_u64(*x as u64);
        }
    }
    fn public_fault(&self) -> Option<&'static str> {
        wf_lookup_fault(self)
    }
}

impl PublicBytes for WfPublic {
    /// `public_bytes(Writer&, const WfPublic&)` (wf.h:106-109).
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.lookups.len() as u64);
        for l in &self.lookups {
            l.public_bytes(w);
        }
        self.message.public_bytes(w);
        w.put_u64(self.message_id as u64);
        w.put_u64(self.stages.len() as u64);
        for s in &self.stages {
            s.public_bytes(w);
        }
        self.choice.public_bytes(w);
    }
    fn public_fault(&self) -> Option<&'static str> {
        wf_public_fault(self)
    }
}

// ------------------------------------------------------------------------------------------------
// What follows from the parameters (wf.h:111-182)
// ------------------------------------------------------------------------------------------------

/// The lookups in the form that LKP takes (`wf_lookups`, wf.h:114-138).
pub fn wf_lookups(x: &WfPublic, m: &WfMatrix) -> Vec<LkpPublic> {
    let mut all = Vec::new();
    for l in &x.lookups {
        let mut p = LkpPublic::default();
        p.d = l.d;
        p.mu = l.mu;
        p.live = l.live;
        for (number, part) in l.parts.iter().enumerate() {
            p.parts.push(part.log_places + m.k_col);
            // Padding is every range of places before, between and after the runs. A place is
            // 2^k_col consecutive key numbers.
            {
                let mut stretch = |from: u64, to: u64| {
                    if from < to {
                        p.padding.push(LkpPadding {
                            part: number as u32,
                            first: from << m.k_col,
                            log_step: 0,
                            length: (to - from) << m.k_col,
                            row: l.padding_key.0,
                        });
                    }
                };
                let mut upto = 0u64;
                for r in &part.runs {
                    stretch(upto, r.first_place);
                    upto = r.first_place + r.places;
                }
                stretch(upto, 1u64 << part.log_places);
            }
        }
        p.read_from = vec![x.message_id];
        p.keys = vec![LkpKeyBlock { first: 0, log_trees: 0, function: 0, padding_row: 0 }];
        p.tables = vec![LkpTablePart { first: 0, log_rows: l.d, function: 0, rows: Vec::new() }];
        p.last_key_level_order = l.first_bound.clone();
        all.push(p);
    }
    all
}

/// Entries of the index-mask message that WF takes (`wf_index_masks`, wf.h:153-157).
pub fn wf_index_masks(x: &WfPublic, m: &WfMatrix) -> usize {
    let mut n = 0usize;
    for p in &wf_lookups(x, m) {
        n += lkp_key_masks(p);
    }
    n
}

/// All entries of the index-mask message that are taken on WF's chain: WF's, and BATT's if there
/// is more than one pending claim (`wf_index_mask_entries`, wf.h:161-165).
pub fn wf_index_mask_entries(x: &WfPublic, m: &WfMatrix) -> usize {
    let mut parts = 0usize;
    for l in &x.lookups {
        parts += l.parts.len();
    }
    wf_index_masks(x, m) + if parts > 1 { batt_masks(m.k_col) } else { 0 }
}

/// Entries of its own oracle message's mask rows that WF takes (`wf_own_masks`, wf.h:167-171).
pub fn wf_own_masks(x: &WfPublic, m: &WfMatrix) -> usize {
    let mut n = 0usize;
    for p in &wf_lookups(x, m) {
        n += lkp_masks(p) - lkp_key_masks(p);
    }
    n
}

/// Linear claims that WF's proximity test batches (`wf_rows_batched`, wf.h:175-182).
pub fn wf_rows_batched(x: &WfPublic, m: &WfMatrix) -> u64 {
    let mut n = x.message.shape.answers as u64;
    for p in &wf_lookups(x, m) {
        n += (p.planes() - 1) as u64
            + (p.part_bits().len() - 1) as u64
            + p.d as u64
            + 1
            + 2
            + 1;
        for &v in p.part_bits() {
            n += v as u64;
        }
    }
    n
}

// ------------------------------------------------------------------------------------------------
// The layout (wf.h:184-209)
// ------------------------------------------------------------------------------------------------

/// A block of plane numbers, placed in the main rows (`WfBlock`, wf.h:190-195).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WfBlock {
    pub lookup: usize,
    /// `(first, log2 of the number)`.
    pub planes: (u32, u32),
    /// log2 of its entries.
    pub bits: u32,
    pub row: u64,
    pub first_place: u64,
}

/// The layout of the multiplicities in the main rows (`wf_layout`, wf.h:196-209).
pub fn wf_layout(x: &WfPublic, ell: u64) -> Vec<WfBlock> {
    let mut blocks = Vec::new();
    for (i, l) in x.lookups.iter().enumerate() {
        let live = if l.live != 0 { l.live } else { 1u32 << l.mu };
        for b in lkp_live_blocks(live) {
            blocks.push(WfBlock { lookup: i, planes: b, bits: b.1 + l.d, row: 0, first_place: 0 });
        }
    }
    blocks.sort_by(|a, b| b.bits.cmp(&a.bits));
    let mut row = 0u64;
    let mut place = 0u64;
    for b in &mut blocks {
        if place + (1u64 << b.bits) > ell {
            row += 1;
            place = 0;
        }
        b.row = row;
        b.first_place = place;
        place += 1u64 << b.bits;
    }
    blocks
}

// ------------------------------------------------------------------------------------------------
// The checks (wf.h:211-306)
// ------------------------------------------------------------------------------------------------

/// `public_fault(const WfRun&)` (wf.h:214).
pub fn wf_run_fault(r: &WfRun) -> Option<&'static str> {
    if r.places < 1 {
        Some("a run covers no place")
    } else {
        None
    }
}

/// `public_fault(const WfPart&)` (wf.h:215-225).
pub fn wf_part_fault(p: &WfPart) -> Option<&'static str> {
    if p.log_places > 40 {
        return Some("a part has too many places");
    }
    let mut upto = 0u64;
    for r in &p.runs {
        if let Some(f) = wf_run_fault(r) {
            return Some(f);
        }
        if r.first_place < upto || r.first_place >= (1u64 << p.log_places) {
            return Some("a part's runs overlap, are not in rising order, or begin beyond the part");
        }
        if r.places > (1u64 << p.log_places) - r.first_place {
            return Some("a run reaches beyond its part");
        }
        upto = r.first_place + r.places;
    }
    if upto == 0 {
        Some("a part covers no place")
    } else {
        None
    }
}

/// `public_fault(const WfLookup&)` (wf.h:226-246).
pub fn wf_lookup_fault(l: &WfLookup) -> Option<&'static str> {
    let planes = if l.live != 0 { l.live } else { 1u32 << l.mu.min(6) };
    if l.mu < 1
        || l.mu > 6
        || l.live >= (1u32 << l.mu)
        || planes < 2
        || planes > 62
        || l.d < 1
        || l.d + planes >= F_BITS
    {
        return Some("a look-up's table or planes are not admitted");
    }
    if l.digit_weight.is_empty() || l.parts.is_empty() {
        return Some("a look-up without a digit or without a part");
    }
    for w in &l.digit_weight {
        if w.0 == 0 {
            // Its entries would enter no key: the look-up would say nothing of them.
            return Some("a digit of a look-up's key has the weight 0");
        }
    }
    if !(l.padding_key.0 >> l.d == 0) {
        return Some("a place of padding holds no row of the table");
    }
    for i in 0..l.first_bound.len() {
        for j in 0..i {
            if l.first_bound[i] == l.first_bound[j] {
                return Some("the order of the last key level names a variable twice");
            }
        }
    }
    for p in &l.parts {
        if let Some(f) = wf_part_fault(p) {
            return Some(f);
        }
        if l.digit_weight.len() == 1 {
            for r in &p.runs {
                if r.stride != 0 {
                    // Nothing would read it: one meaning, one encoding.
                    return Some("a run has a stride where a key has one digit");
                }
            }
        }
        if l.digit_weight.len() > 1 {
            for r in &p.runs {
                if r.stride == 0 {
                    // A key of several digits would then be a multiple of one entry.
                    return Some("the digits of a key lie in one row");
                }
            }
        }
    }
    None
}

/// `public_fault(const WfPublic&)` (wf.h:247-254).
pub fn wf_public_fault(x: &WfPublic) -> Option<&'static str> {
    if x.lookups.is_empty() {
        return Some("no look-up");
    }
    let s = &x.message.shape;
    if s.main_rows == 0 || s.mask_rows == 0 || s.main_deg != 1 || s.answers < 1 {
        return Some("the oracle message has not main rows over F and mask rows, or is not sampled");
    }
    for l in &x.lookups {
        if let Some(f) = wf_lookup_fault(l) {
            return Some(f);
        }
    }
    None
}

/// Whether the keys of this lookup are `offset +` one entry (one digit, of weight 1) and its runs
/// cover every row of the matrix (`wf_covers_all_rows`, wf.h:257-270).
pub fn wf_covers_all_rows(x: &WfPublic, lookup: usize, m: &WfMatrix) -> bool {
    let l = &x.lookups[lookup];
    if l.digit_weight.len() != 1 || !(l.digit_weight[0] == F::one()) {
        return false;
    }
    let mut stretch: Vec<(u64, u64)> = Vec::new();
    for p in &l.parts {
        for r in &p.runs {
            stretch.push((r.first_row, r.first_row + r.places));
        }
    }
    stretch.sort();
    let mut upto = 0u64;
    for s in &stretch {
        if s.0 > upto {
            return false;
        }
        upto = core::cmp::max(upto, s.1);
    }
    upto >= m.rows
}

/// `public_fault(x)`, then whether x fits the matrix and the codes (`wf_fault`, wf.h:274-306).
pub fn wf_fault(codes: &Codes, x: &WfPublic, m: &WfMatrix) -> Option<&'static str> {
    if let Some(f) = wf_public_fault(x) {
        return Some(f);
    }
    if m.rows < 1 || m.k_row() > 40 || m.k_col > 40 {
        return Some("a matrix without rows, or with too many rows or columns");
    }
    for l in &x.lookups {
        let planes = if l.live != 0 { l.live } else { 1u32 << l.mu };
        let mut keys = 0u64;
        for p in &l.parts {
            let v = p.log_places + m.k_col;
            if v < 1 || v >= planes {
                return Some("a part has no key, or more keys than a multiplicity can count");
            }
            // The last key level of a part of 2^v keys has v - 1 variables.
            for &variable in &l.first_bound {
                if variable + 1 >= v {
                    return Some("the order of the last key level names a variable that a part has not");
                }
            }
            for r in &p.runs {
                if r.stride > m.rows || r.first_row >= m.rows || r.places > m.rows - r.first_row {
                    return Some("a run's places reach beyond the matrix");
                }
                if (l.digit_weight.len() - 1) as u64 * r.stride > m.rows - r.first_row - r.places {
                    return Some("a run's places reach beyond the matrix");
                }
            }
            keys += 1u64 << v;
            if keys >> planes != 0 {
                return Some("a look-up has more keys than a multiplicity can count");
            }
        }
    }
    // Some lookup whose keys are single entries must cover every row: WF is about every entry.
    let mut covered = false;
    for i in 0..x.lookups.len() {
        covered = covered || wf_covers_all_rows(x, i, m);
    }
    if !covered {
        return Some("no look-up of the ranges covers every row of the matrix");
    }
    let s = &x.message.shape;
    if s.code as usize >= codes.base.len() || s.mask_code as usize >= codes.mask.len() {
        return Some("the oracle message names a code that is not there");
    }
    let ell = codes.base[s.code as usize].ell as u64;
    let blocks = wf_layout(x, ell);
    if (1u64 << blocks[0].bits) > ell {
        // The largest comes first.
        return Some("a block of planes is longer than a main row");
    }
    if blocks.last().unwrap().row + 1 != s.main_rows as u64 {
        return Some("the oracle message has not the main rows that the multiplicities fill");
    }
    let free = free_mask_entries(s.mask_rows, codes.mask[s.mask_code as usize].ell, s.answers);
    if wf_own_masks(x, m) as u64 > free {
        return Some("the mask rows have no room for the look-ups' masks and the pad");
    }
    if x.stages.is_empty()
        || x.stages[0].code != s.code
        || x.stages[0].mask_code != s.mask_code
    {
        return Some("the first stage of the proximity test has not the oracle message's codes");
    }
    let mut stage = 0usize;
    // The code switches' messages get as many sample answers as this one: the plan's `set.samples`.
    iopp_fault(codes, &x.stages, s.answers, &mut stage)
}

/// The first fold of WF's proximity test; its mask shares the tree of WF's oracle message
/// (`wf_first_fold`, wf.h:309-313).
pub fn wf_first_fold(x: &WfPublic) -> FoldShape {
    let mut f = iopp_fold_shape(&x.stages[0], Default::default());
    f.mask_leaf_class = x.message.leaf_class;
    f
}

/// The oracle messages of WF's prover message, in order (`wf_message`, wf.h:315-319).
pub fn wf_message(x: &WfPublic) -> Vec<OracleNotice> {
    let mut m = vec![x.message.clone()];
    if x.choice.masks_ride {
        m.push(fold_mask_notice(&wf_first_fold(x)));
    }
    m
}

/// The function by which LKP adds a vector on lookup i's multiplicities to a linear claim
/// (`wf_planes_at`, wf.h:323-338).
pub fn wf_planes_at(x: &WfPublic, codes: &Codes, i: usize) -> LkpPlanesAt {
    let s = &x.message.shape;
    let log_ell = codes.base[s.code as usize].log_ell();
    let row_bits = ceil_log2(s.main_rows as u64);
    let mu = x.lookups[i].mu;
    let o = x.message_id;
    let mut mine: Vec<WfBlock> = Vec::new();
    for b in wf_layout(x, codes.base[s.code as usize].ell as u64) {
        if b.lookup == i {
            mine.push(b);
        }
    }
    Rc::new(move |row: &mut Row, v: Tensor| {
        for b in &mine {
            let mut part = lkp_on_block(&v, mu, b.planes);
            // Where the block begins in its row.
            part.insert_choice(b.bits, log_ell - b.bits, b.first_place >> b.bits);
            // The row's number is the low bits of a table's index.
            part.insert_choice(0, row_bits, b.row);
            row.add(o, Part::Main, part);
        }
    })
}

/// Appends to `g` the row weights `scale * values[first + i]` on matrix rows `first_row + i`,
/// `i < count`, and 0 elsewhere (`wf_weights_on_rows`, wf.h:344-362). `values` is shared, not
/// copied. Not checked: that the rows are inside the matrix (`wf_fault` checks the runs).
pub fn wf_weights_on_rows(
    k_row: u32,
    first_row: u64,
    values: &Rc<Vec<E>>,
    first: u64,
    count: u64,
    scale: E,
    g: &mut Vec<Tensor>,
) {
    let mut at = first_row;
    let end = first_row + count;
    while at < end {
        // The largest aligned block that begins at `at` and ends by `end`.
        let mut d = 0u32;
        while d < k_row && (at & ((2u64 << d) - 1)) == 0 && at + (2u64 << d) <= end {
            d += 1;
        }
        let mut t = Tensor::default();
        if d == 0 {
            t.scalar = values[(first + (at - first_row)) as usize] * scale;
            t.insert_choice(0, k_row, at);
        } else {
            t.scalar = scale;
            t.push_dense(d);
            t.insert_choice(d, k_row - d, at >> d);
            t.set_values(values.clone(), first + (at - first_row));
        }
        g.push(t);
        at += 1u64 << d;
    }
}

/// The pending claim of one part (`wf_pending_row`, wf.h:378-407):
/// `sum over the key numbers i of weights[i] * key[i] + <masks> = target`.
pub fn wf_pending_row(m: &WfMatrix, l: &WfLookup, p: &WfPart, claim: LkpKeys) -> TensorRow {
    assert!(
        claim.point.len() == m.k_col as usize + p.log_places as usize,
        "WF: the claim's point has not one coordinate for each bit of a key's number"
    );
    // eq(z_place, .), coordinate t for bit t of the place.
    let mut e: Rc<Vec<E>> = Rc::new(vec![E::one()]);
    for t in 0..p.log_places {
        let z = claim.point[m.k_col as usize + t as usize];
        let half = e.len();
        let v = Rc::make_mut(&mut e);
        v.resize(2 * half, E::zero());
        for i in 0..half {
            let base = v[i];
            let hi = base * z;
            v[half + i] = hi;
            v[i] = base - hi;
        }
    }
    let mut row = TensorRow { g: Vec::new(), psi: Vec::new(), masks: Vec::new(), target: E::zero() };
    let mut covered = E::zero();
    for r in &p.runs {
        for i in 0..r.places {
            covered += e[(r.first_place + i) as usize];
        }
        for q in 0..l.digit_weight.len() {
            wf_weights_on_rows(
                m.k_row(),
                r.first_row + q as u64 * r.stride,
                &e,
                r.first_place,
                r.places,
                E::from_base(l.digit_weight[q]),
                &mut row.g,
            );
        }
    }
    // The sum of all weights in LKP's claim.
    let mut handed = E::zero();
    for t in &claim.weights.tensors {
        assert!(!t.has_dense(), "WF: LKP's weights are product forms and single entries");
        let mut sum = t.scalar;
        for i in 0..t.vars() {
            sum = sum * (t.lo(i) + t.hi(i));
        }
        handed += sum;
    }
    for entry in &claim.weights.entries {
        handed += entry.1;
    }
    assert!(handed == covered, "WF: LKP's weights lie on other places than the runs cover");
    row.psi = claim.point[..m.k_col as usize].to_vec();
    row.target = claim.target - covered * l.offset;
    row.masks = claim.masks;
    row
}

// ------------------------------------------------------------------------------------------------
// The two sides (wf.h:422-606)
// ------------------------------------------------------------------------------------------------

/// The pending claims that WF leaves on the matrix (`WfPending`, wf.h:433-451). Every claim must
/// be taken; the drop check panics if one is left and the channel has not been reported rejected
/// (the port's stand-in for C++'s `channel_->ok()`, which `VerifierRounds` does not expose).
pub struct WfPending {
    rows: Vec<TensorRow>,
    rejected: Rc<Cell<bool>>,
}

impl Default for WfPending {
    fn default() -> Self {
        WfPending { rows: Vec::new(), rejected: Rc::new(Cell::new(false)) }
    }
}

impl WfPending {
    /// `put`: the channel must outlive this in C++; here a rejected channel is reported by
    /// `channel_rejected`.
    pub fn put(&mut self, row: TensorRow) {
        self.rows.push(row);
    }
    pub fn size(&self) -> usize {
        self.rows.len()
    }
    /// For tests and reports.
    pub fn look(&self) -> &[TensorRow] {
        &self.rows
    }
    pub fn take(&mut self) -> Vec<TensorRow> {
        core::mem::take(&mut self.rows)
    }
    /// Reports that the channel has rejected the proof (`!channel_->ok()` at drop).
    pub fn channel_rejected(&self) {
        self.rejected.set(true);
    }
}

impl Drop for WfPending {
    fn drop(&mut self) {
        assert!(
            self.rows.is_empty() || self.rejected.get(),
            "WF: the rows on the matrix were dropped: no test on the table has taken them"
        );
    }
}

/// What WF returns (`WfOutput`, wf.h:453-457).
pub struct WfOutput {
    pub pending: WfPending,
    pub message: OracleId,
    pub group: GroupId,
}

impl Default for WfOutput {
    fn default() -> Self {
        WfOutput { pending: WfPending::default(), message: NONE_ID, group: NONE_ID }
    }
}

/// The pass-key of `wf_rows_verify` (`WfRowsAlone`, wf.h:499-506): only this module (and, in C++,
/// a file that defines `BLK_WF_ROWS_FOR_A_TEST`) constructs one.
pub struct WfRowsAlone(());

/// Both sides begin with this (`wf_start_check`, wf.h:464-469).
pub fn wf_start_check(st: &Statement, x: &WfPublic, m: &WfMatrix, index_masks: OracleId) {
    let fault = wf_fault(st.codes(), x, m);
    assert!(fault.is_none(), "WF: {}", fault.unwrap_or(""));
    assert!(
        st.oracle(index_masks).sampled && st.oracle(index_masks).shape.main_rows == 0,
        "WF: the index-mask message is a sampled message of mask rows alone, sent before WF begins"
    );
}

/// WF without its proximity test, the verifier's side (`wf_rows_verify`, wf.h:576-599).
#[allow(clippy::too_many_arguments)]
pub fn wf_rows_verify(
    _: &WfRowsAlone,
    V: &mut VerifierContext<'_, '_, '_, '_>,
    fixed: &Public<WfPublic>,
    table: &LinPublic,
    index_masks: OracleId,
    out: &mut WfOutput,
    first_mask: &mut FoldMask,
    calls: &mut HashCalls,
) -> bool {
    let x = V.ch.get(fixed);
    let m = wf_matrix_of(V.ch.get(&table.shape));
    wf_start_check(&V.st, x, &m, index_masks);
    assert!(
        x.message.shape.answers == V.ch.plan().set.samples,
        "WF: the oracle message has another number of answers to a sample than the plan's setting"
    );
    let s = &x.message.shape;
    let (sent, ids) = send_verify(V, &wf_message(x), AnswersRound::Own, calls);
    if !sent {
        if !V.ch.ok() {
            out.pending.channel_rejected();
        }
        return false;
    }
    assert!(
        ids[0] == x.message_id,
        "WF: the oracle message has another number on this channel than the parameters say"
    );
    if x.choice.masks_ride {
        first_mask.sent_as(ids[1]);
    }
    out.message = ids[0];
    out.group = V.st.new_group("ranges", s.code, s.mask_code);
    V.st.join(out.group, out.message, false);

    let lookups: Public<Vec<LkpPublic>> = derive(fixed, &table.shape, |r, t: &LinShape| {
        wf_lookups(r, &wf_matrix_of(t))
    });
    for i in 0..x.lookups.len() {
        let mut left = LkpOutput::default();
        let planes = wf_planes_at(x, V.st.codes(), i);
        let good = lkp_verify(
            V,
            &element(&lookups, i),
            &planes,
            out.message,
            out.group,
            &mut left,
            index_masks,
            calls,
        );
        if !good {
            if !V.ch.ok() {
                out.pending.channel_rejected();
            }
            return false;
        }
        for part in 0..x.lookups[i].parts.len() {
            let claim = left.keys.take(part);
            let row = wf_pending_row(&m, &x.lookups[i], &x.lookups[i].parts[part], claim);
            out.pending.put(row);
        }
    }
    true
}

/// WF, the verifier's side (`wf_verify`, wf.h:601-606).
pub fn wf_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    fixed: &Public<WfPublic>,
    table: &LinPublic,
    index_masks: OracleId,
    out: &mut WfOutput,
    calls: &mut HashCalls,
) -> bool {
    let mut first_mask = FoldMask::default();
    if !wf_rows_verify(&WfRowsAlone(()), V, fixed, table, index_masks, out, &mut first_mask, calls) {
        return false;
    }
    let x = V.ch.get(fixed);
    let stages = x.stages.clone();
    let choice = x.choice;
    let good = iopp_verify(V, out.group, &stages, choice, first_mask, calls);
    if !good && !V.ch.ok() {
        out.pending.channel_rejected();
    }
    good
}
