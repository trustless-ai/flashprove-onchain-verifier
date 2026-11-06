//! The sizes of WF, the committer's range proof, ported from `blocks/frame/wf_frame.h`.
//!
//! This file begins with the shapes `wf_units.rs` builds; `wf_cut`, `wf_lines`, `wf_sized` and
//! `wf_plan` follow with the other frame lanes.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::frame::derive::{shape_of, solve_group, solve_test, TestSizes};
use crate::frame::lin_frame::lin_group_bits;
use crate::iop::member::plan_member_rows;
use crate::frame::parameters::GroupLine;
use crate::iop::context::tree_sizes;
use crate::iop::iopp::{iopp_sized_fault, iopp_stages};
use crate::iop::relation::{Codes, OracleId};
use crate::iop::send_pad::{mask_rows_for, sample_cube};
use crate::iop::wf::{
    wf_fault, wf_layout, wf_lookups, wf_message, wf_own_masks, wf_rows_batched, WfLookup,
    WfMatrix, WfPart, WfPublic, WfRun,
};
use crate::numbers::blocks::{
    plan_iopp, plan_lookup, plan_send, stage_cube_bits, GroupLoad, LookupSize, SampleSize,
    TestedIn,
};
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::Plan;
use crate::numbers::setting::{Scope, Setting};

/// One lookup before it is cut into parts (`WfShapeLookup`, wf_frame.h:32-36).
#[derive(Clone, Debug, Default)]
pub struct WfShapeLookup {
    /// `parts` is not read; `mu` and `live` must be 0: `wf_lines` sets them.
    pub lookup: WfLookup,
    /// All entries, in order; `first_place` is not read.
    pub entries: Vec<WfRun>,
    /// If > 0: an entry has 2^log_rows_apart rows, each a one-digit key.
    pub log_rows_apart: u32,
}

/// What WF looks up (`WfShape`, wf_frame.h:39-43). The matrix has `matrix_rows` rows and 2^k_col
/// columns.
#[derive(Clone, Debug, Default)]
pub struct WfShape {
    pub k_col: u32,
    pub matrix_rows: u64,
    pub lookups: Vec<WfShapeLookup>,
}

/// The largest number of parts of one lookup (`WF_MOST_PARTS`, wf_frame.h:95).
pub const WF_MOST_PARTS: u64 = 256;

/// `wf_cut()` (wf_frame.h:49-69).
pub fn wf_cut(entries: &[WfRun], log_places: u32, log_rows_apart: u32) -> Vec<WfPart> {
    assert!(
        log_rows_apart <= log_places && log_places < 63,
        "wf_cut: a part is smaller than an entry"
    );
    let most = 1u64 << (log_places - log_rows_apart);
    let mut cut: Vec<Vec<WfRun>> = Vec::new();
    let mut room = 0u64;
    for r0 in entries {
        let mut r = *r0;
        while r.places != 0 {
            if room == 0 {
                cut.push(Vec::new());
                room = most;
            }
            let take = core::cmp::min(room, r.places);
            cut.last_mut().unwrap().push(WfRun {
                first_place: most - room,
                first_row: r.first_row,
                places: take,
                stride: r.stride,
            });
            r.first_row += take;
            r.places -= take;
            room -= take;
        }
    }
    let mut parts = Vec::new();
    for one in &cut {
        let mut p = WfPart { log_places, runs: Vec::new() };
        for q in 0..(1u64 << log_rows_apart) {
            for r in one {
                p.runs.push(WfRun {
                    first_place: q * most + r.first_place,
                    first_row: r.first_row + q * r.stride,
                    places: r.places,
                    stride: if log_rows_apart != 0 { 0 } else { r.stride },
                });
            }
        }
        parts.push(p);
    }
    parts
}

/// `wf_parts_of()` (wf_frame.h:97-106): how many parts `wf_cut` would make.
pub fn wf_parts_of(entries: &[WfRun], log_places: u32, log_rows_apart: u32) -> u64 {
    assert!(
        log_rows_apart <= log_places && log_places < 63,
        "wf_cut: a part is smaller than an entry"
    );
    let most = 1u64 << (log_places - log_rows_apart);
    let mut whole = 0u64;
    let mut left = 0u64;
    for r in entries {
        whole += r.places / most;
        left += r.places % most;
        whole += left / most;
        left %= most;
    }
    whole + if left != 0 { 1 } else { 0 }
}

/// `wf_planes_of()` (wf_frame.h:122-128).
pub fn wf_planes_of(parts: &[WfPart], k_col: u32) -> u32 {
    let mut planes = 2u32;
    let mut keys = 0u64;
    for p in parts {
        planes = core::cmp::max(planes, p.log_places + k_col + 1);
        keys += 1u64 << core::cmp::min(p.log_places + k_col, 62);
    }
    while planes < 63 && (keys >> planes) != 0 {
        planes += 1;
    }
    planes
}

/// The cut lookups and their planes (`WfLines`, wf_frame.h:108-117).
#[derive(Clone, Debug)]
pub struct WfLines {
    pub k_col: u32,
    pub matrix_rows: u64,
    pub lookups: Vec<WfLookup>,
    /// Of the oracle message with the multiplicities.
    pub group: GroupLine,
    /// If true, the mask of the proximity test's first fold is sent with the multiplicities.
    pub masks_ride: bool,
    /// After the index-mask message.
    pub message_id: OracleId,
    /// Not null: `wf_sized` rejects the shape with this message.
    pub fault: Option<&'static str>,
}

impl Default for WfLines {
    fn default() -> Self {
        WfLines {
            k_col: 0,
            matrix_rows: 0,
            lookups: Vec::new(),
            group: GroupLine::default(),
            masks_ride: true,
            message_id: 1,
            fault: None,
        }
    }
}

/// `wf_lines()` (wf_frame.h:135-158). `part_log` is the parameter file's `ranges-part`.
pub fn wf_lines(shape: &WfShape, group: &GroupLine, part_log: u32) -> WfLines {
    let mut l = WfLines {
        k_col: shape.k_col,
        matrix_rows: shape.matrix_rows,
        group: group.clone(),
        ..WfLines::default()
    };
    if part_log > ceil_log2(core::cmp::max(shape.matrix_rows, 1)) {
        l.fault = Some("a part would read more rows than the matrix has: the line ranges-part is too large for this matrix");
    }
    for s in &shape.lookups {
        let mut look = s.lookup.clone();
        let digits = ceil_log2(core::cmp::max(s.lookup.digit_weight.len() as u64, 1));
        look.parts.clear();
        if l.fault.is_none()
            && part_log >= digits
            && part_log - digits >= s.log_rows_apart
            && part_log < 63
        {
            if wf_parts_of(&s.entries, part_log - digits, s.log_rows_apart) > WF_MOST_PARTS {
                l.fault = Some("a look-up would have more than 256 parts: the line ranges-part is too small for this matrix");
            } else {
                look.parts = wf_cut(&s.entries, part_log - digits, s.log_rows_apart);
            }
        }
        if look.mu != 0 || look.live != 0 {
            l.fault = Some("a look-up's planes follow from its parts: whoever gives the shape leaves them 0");
        }
        let planes = wf_planes_of(&look.parts, shape.k_col);
        look.mu = core::cmp::max(1, ceil_log2(planes as u64));
        look.live = if planes == (1u32 << look.mu) { 0 } else { planes };
        l.lookups.push(look);
    }
    l
}

/// `x`: WF's public parameters; `test`: its proximity test's sizes (`WfSized`, wf_frame.h:161-178).
#[derive(Clone, Debug, Default)]
pub struct WfSized {
    pub lines: WfLines,
    /// The matrix's size as `lines` has it; it sizes the mask rows and the plan.
    pub matrix: WfMatrix,
    pub x: WfPublic,
    pub test: TestSizes,
    /// Pending claims on the matrix that WF leaves: one for each part.
    pub pending: usize,
    /// Not empty: why these inputs give no valid sizes.
    pub refused: String,
}

/// `wf_sized()` (wf_frame.h:181-217). `codes`: the caller's list; the codes of WF's proximity test
/// are added to it where missing.
pub fn wf_sized(s: &Setting, l: &WfLines, codes: &mut Codes) -> WfSized {
    let mut z = WfSized { lines: l.clone(), ..WfSized::default() };
    if let Some(f) = l.fault {
        z.refused = format!("ranges: {}", f);
        return z;
    }
    let m = WfMatrix { k_col: l.k_col, rows: l.matrix_rows };
    z.matrix = m;
    z.x.lookups = l.lookups.clone();
    z.x.message_id = l.message_id;
    z.x.choice.masks_ride = l.masks_ride;
    if l.lookups.is_empty() {
        z.refused = String::from("ranges: no look-up");
        return z;
    }
    for look in &l.lookups {
        if look.mu < 1
            || look.mu > 6
            || look.live > (1u32 << look.mu)
            || look.d < 1
            || look.d > 40
            || look.parts.is_empty()
        {
            z.refused = String::from("ranges: a look-up's table, planes or parts are not admitted");
            return z;
        }
        z.pending += look.parts.len();
    }
    let ell = 1u64 << l.group.log_ell;
    let ell_zk = 1u64 << l.group.mask_log_ell;
    {
        let o = &mut z.x.message.shape;
        o.name = String::from("multiplicities of the ranges' look-ups");
        o.main_deg = 1;
        o.answers = s.samples;
    }
    let blocks = wf_layout(&z.x, ell);
    for b in &blocks {
        if (1u64 << b.bits) > ell {
            z.refused = String::from("once-ranges: a block of planes is longer than a main row");
            return z;
        }
    }
    z.x.message.shape.main_rows = blocks.last().unwrap().row as usize + 1;
    if ell_zk <= s.samples as u64 {
        z.refused = String::from("once-ranges: a mask row is shorter than the pad");
        return z;
    }
    z.x.message.shape.mask_rows =
        mask_rows_for(wf_own_masks(&z.x, &m) as u64, ell_zk as usize, s.samples);
    if z.x.message.shape.mask_rows == 0 {
        z.refused =
            String::from("once-ranges: no number of mask rows has room for the look-ups' masks");
        return z;
    }

    let (k, h) = lin_group_bits(&[&z.x.message.shape]);
    z.test.group = shape_of("once-ranges", &l.group, k, false);
    z.test.group.h = h;
    let load = GroupLoad {
        cube_bits: stage_cube_bits(&z.test.group),
        messages: 1,
        batched_rows: wf_rows_batched(&z.x, &m),
    };
    let mut why = String::new();
    if !solve_group(s, Scope::Once, &load, |t| t, &mut z.test, &mut why) {
        z.refused = why;
        return z;
    }
    if !solve_test(s, Scope::Once, &l.group, &mut z.test, &mut why) {
        z.refused = why;
        return z;
    }
    z.x.stages = iopp_stages(&z.test.stages, codes);
    z.x.message.shape.code = z.x.stages[0].code;
    z.x.message.shape.mask_code = z.x.stages[0].mask_code;
    if let Some(f) = wf_fault(codes, &z.x, &m) {
        z.refused = format!("ranges: {}", f);
    }
    z
}

/// WF's rounds in the one-time chain, after the index-mask message is sent and sampled: WF, then,
/// if WF leaves more than one pending claim, BATT (`wf_plan`, wf_frame.h:226-236). `z.refused` must
/// be empty: this is not checked. `last` numbers marked trees (`OneList`), as `OneList::mark`
/// expects; the C++ header keeps that counter in a static.
pub fn wf_plan(p: &mut Plan, codes: &Codes, z: &WfSized, last: &mut u64) {
    let x = &z.x;
    let trees = tree_sizes(codes, &wf_message(x), last);
    // the copy of the group from which `plan_iopp` computes the errors
    plan_send(
        p,
        "ranges: multiplicities",
        &[SampleSize {
            cube_bits: sample_cube(codes, &x.message.shape).bits,
            groups: TestedIn::new(&z.test.stages[0].g),
        }],
        trees.len() as u32,
        true,
    );
    let lookups = wf_lookups(x, &z.matrix);
    for i in 0..lookups.len() {
        plan_lookup(
            p,
            &format!("ranges: {}", x.lookups[i].name),
            &LookupSize {
                v: 0,
                d: lookups[i].d,
                mu: lookups[i].mu,
                shifted: false,
                live: lookups[i].live,
                parts: lookups[i].parts.clone(),
            },
        );
    }
    if let Some(fault) = iopp_sized_fault(codes, &x.stages, &z.test.stages) {
        // is `codes` the list that `wf_sized` filled?
        p.refuse(&format!("ranges: {}", fault));
        return;
    }
    plan_iopp(
        p,
        "ranges",
        &z.test.stages,
        &trees,
        wf_rows_batched(x, &z.matrix),
        if x.choice.masks_ride { 0 } else { 1 },
        x.choice.masks_ride,
        last,
    );
    plan_member_rows(p, "ranges: rows on the table", z.pending as u64, z.matrix.k_col);
}
