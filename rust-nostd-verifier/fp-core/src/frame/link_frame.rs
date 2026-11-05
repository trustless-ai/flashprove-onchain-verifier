//! Sizing of LINK, the proof that a leaf table has the anchor's entries
//! (`blocks/frame/link_frame.h`).
//!
//! The group contains the two folded rows: each table's rows, combined at one random point. The
//! numbers of columns follow from the tables' distances; `link_sized` solves the group and the
//! proximity test. `link_plan` follows with the plan emitters.

use alloc::format;
use alloc::string::String;

use crate::code::code::Code;
use crate::frame::derive::{shape_of, solve_group, solve_test, TestSizes};
use crate::frame::lin_frame::lin_rows_of;
use crate::frame::parameters::{GroupLine, Parameters};
use crate::iop::context::tree_sizes;
use crate::iop::foldeq::{index_fault, IndexShape};
use crate::iop::iopp::{iopp_sized_fault, iopp_stages};
use crate::iop::link::{link_fault, link_message, LinkShape};
use crate::iop::relation::Codes;
use crate::iop::send_pad::sample_cube;
use crate::numbers::blocks::{
    analysis_table, plan_iopp, plan_link, scope_positions, stage_cube_bits, table_admitted,
    GroupLoad, SampleSize, TableSize, TestedIn, TreeSize,
};
use crate::numbers::plan::Plan;
use crate::numbers::real::Bound;
use crate::numbers::setting::{Scope, Setting};

/// LINK's free parameters (`LinkLines`, link_frame.h:30-38).
#[derive(Clone, Debug)]
pub struct LinkLines {
    pub table_rows_log: u32,
    pub table_log_n: u32,
    pub table_data: u64,
    pub table_random: u64,
    /// The group of the two folded rows.
    pub folded: GroupLine,
    pub rows_high: bool,
    pub masks_ahead: bool,
    pub masks_ride: bool,
}

impl Default for LinkLines {
    /// The C++ member defaults (link_frame.h:34-37): the three flags are true.
    fn default() -> Self {
        LinkLines {
            table_rows_log: 0,
            table_log_n: 0,
            table_data: 0,
            table_random: 0,
            folded: GroupLine::default(),
            rows_high: true,
            masks_ahead: true,
            masks_ride: true,
        }
    }
}

/// What a run needs of LINK (`LinkSized`, link_frame.h:49-55).
#[derive(Clone, Debug, Default)]
pub struct LinkSized {
    pub lines: LinkLines,
    pub s: LinkShape,
    pub table: TableSize,
    pub linked: TestSizes,
    /// Not empty: no admissible numbers follow.
    pub refused: String,
}

/// `link_lines()` (link_frame.h:42-47): the committer proves LINK, so the group uses the parameter
/// file's `once-folded`, like the one-time test's folded row.
pub fn link_lines(p: &Parameters) -> LinkLines {
    LinkLines {
        table_rows_log: p.table_rows_log,
        table_log_n: p.table_log_n,
        table_data: p.table_data,
        table_random: p.table_random,
        folded: p.once_folded.clone(),
        rows_high: true,
        masks_ahead: true,
        masks_ride: true,
    }
}

/// `link_table()` (link_frame.h:60-66): the tables with distances given as radii in positions.
pub fn link_table(s: &Setting, l: &LinkLines, radius: u64, later_radius: u64) -> TableSize {
    let mut t = TableSize::default();
    t.code.name = String::from("table");
    t.code.log_n = l.table_log_n;
    t.code.ell = l.table_data;
    t.code.r = l.table_random;
    t.v = l.table_rows_log;
    t.answers = s.samples;
    t.distances.radius = radius;
    t.distances.later_radius = later_radius;
    t
}

/// `link_sized()` (link_frame.h:70-113). `table`: the tables that `l` describes, with their
/// distances; for a parameter file, `derive_table` makes it. `codes`: the chain's list; LINK's
/// codes are added if missing.
pub fn link_sized(s: &Setting, l: &LinkLines, table: &TableSize, codes: &mut Codes) -> LinkSized {
    let mut x = LinkSized { lines: l.clone(), table: table.clone(), ..LinkSized::default() };
    let mut why = String::new();
    let mut shape = LinkShape::default();

    // ---- the tables and their columns ----
    if x.table.code.log_n != l.table_log_n
        || x.table.code.ell != l.table_data
        || x.table.code.r != l.table_random
        || x.table.v != l.table_rows_log
    {
        x.refused = String::from("table: the distances belong to another table");
        return x;
    }
    if x.table.code.dim(s) > x.table.code.n() {
        x.refused = String::from("table: data and random coordinates exceed the code's length");
        return x;
    }
    let a = analysis_table(s, &x.table);
    if !table_admitted(&x.table, &a) {
        x.refused = String::from("table: the distances are not admitted");
        return x;
    }
    shape.columns_first = scope_positions(s, Scope::Once, &a.later.agree, &Bound::from_u64(0));
    shape.columns_further = scope_positions(s, Scope::Once, &a.once.agree, &Bound::from_u64(0));
    if shape.columns_first == 0 || shape.columns_further == 0 {
        x.refused = String::from("table: no number of columns reaches the target");
        return x;
    }

    // ---- shapes ----
    let index = IndexShape {
        code: Code {
            log_n: l.table_log_n,
            ell: l.table_data as usize,
            r: l.table_random as usize,
        },
        v: l.table_rows_log,
        answers: s.samples,
        salt_bytes: s.salt_bytes as usize,
        distances: x.table.distances,
    };
    if let Some(f) = index_fault(&index) {
        x.refused = format!("table: {}", f);
        return x;
    }
    let answers = index.answers;
    shape.table = index;
    shape.rows_high = l.rows_high;
    shape.masks_ahead = l.masks_ahead;
    shape.choice.masks_ride = l.masks_ride;
    shape.rows = lin_rows_of(
        shape.first(s.samples).entries() + s.samples as u64,
        1u64 << l.folded.log_ell,
        l.rows_high,
    ) as u64;
    let group = shape.test()[0]; // its numbers of row variables; the codes come below
    x.linked.group = shape_of("linked", &l.folded, group.k, true);
    x.linked.group.h = group.h;

    // ---- positions and random coordinates; stages; codes ----
    // batched_rows: for each table, one linear claim per record answer and one per drawn column; the
    // equality of the two folded rows; one per answer to their samples.
    let load = GroupLoad {
        cube_bits: stage_cube_bits(&x.linked.group),
        messages: 2,
        batched_rows: 2 * answers as u64
            + shape.columns_first
            + shape.columns_further
            + 1
            + 2 * s.samples as u64,
    };
    if !solve_group(s, Scope::Once, &load, |t| t, &mut x.linked, &mut why) {
        x.refused = why;
        return x;
    }
    if !solve_test(s, Scope::Once, &l.folded, &mut x.linked, &mut why) {
        x.refused = why;
        return x;
    }
    let test = iopp_stages(&x.linked.stages, codes);
    assert!(
        test.len() >= 2 && test[0].k == group.k && test[0].h == group.h,
        "link_frame: the solved first stage is not the group"
    );
    shape.code = test[0].code;
    shape.mask_code = test[0].mask_code;
    shape.later = test[1..].to_vec();
    if let Some(f) = link_fault(codes, &shape, s.samples) {
        x.refused = format!("LINK: {}", f);
    }
    x.s = shape;
    x
}

/// `link_plan()` (link_frame.h:118-129). Adds LINK's rounds to `p`, up to the proximity test's end.
/// `table_tree`: sizes of the tree over one table's columns. Not checked: `x.refused` is empty.
/// `last` numbers marked trees (`OneList`), as `OneList::mark` expects; the C++ header keeps that
/// counter in a static.
pub fn link_plan(p: &mut Plan, codes: &Codes, x: &LinkSized, table_tree: &TreeSize, last: &mut u64) {
    let shape = &x.s;
    let u = SampleSize {
        cube_bits: sample_cube(codes, &shape.first(p.set.samples).u).bits,
        groups: TestedIn::new(&x.linked.stages[0].g),
    };
    let (first, further) = plan_link(p, "link", &x.table, &u, table_tree);
    if !p.refused() {
        assert!(
            first == shape.columns_first && further == shape.columns_further,
            "link_frame: the plan draws other numbers of columns"
        );
    }
    // `plan_iopp` computes errors from x's solved stages: they must match S's under `codes`
    let fault = iopp_sized_fault(codes, &shape.test(), &x.linked.stages);
    assert!(fault.is_none(), "{}", fault.unwrap_or(""));
    plan_iopp(
        p,
        "the two folded rows",
        &x.linked.stages,
        &tree_sizes(codes, &link_message(shape, p.set.samples), last),
        2 * shape.table.answers as u64 + first + further + 1 + 2 * p.set.samples as u64,
        if shape.masks_ahead { 0 } else { 1 },
        shape.choice.masks_ride,
        last,
    );
}
