//! The sizes that the parameter file does not state, ported from `blocks/frame/derive.h`.
//!
//! For a group these are its slack and distance, the number of positions, the length of its codes'
//! random tails and the test's stages. `derive` does this for a request's segments and sets the
//! committed table's distances; `lin_frame`, `link_frame` and `wf_frame` size their groups with
//! these functions. `configure` rejects the parameters unless every round planned from these sizes
//! meets the error target, proof of work counted.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::frame::parameters::{GroupLine, Parameters};
use crate::numbers::blocks::{
    analysis_group, group_holds, positions_from_below, scope_positions, size_group, size_recorded_table,
    stage_cube_bits, GroupLoad, GroupSize, Stage, TableSize,
};
use crate::numbers::codes::{tail_for, CodeSize};
use crate::numbers::plan::Plan;
use crate::numbers::real::{Bound, Real};
use crate::numbers::setting::{Scope, Setting};

/// What the sizes need of the sub-proofs' shapes (`FrameShape`, derive.h:32-40).
#[derive(Clone, Debug)]
pub struct FrameShape {
    pub link_rows_log: u32,
    pub last_rows_log: u32,
    pub link_cube_bits: u32,
    pub link_slots: u64,
    pub link_messages: u32,
    pub link_batched_rows: u64,
    pub index_rows: u64,
}

impl Default for FrameShape {
    fn default() -> Self {
        FrameShape {
            link_rows_log: 8,
            last_rows_log: 1,
            link_cube_bits: 0,
            link_slots: 1,
            link_messages: 8,
            link_batched_rows: 1 << 16,
            index_rows: 0,
        }
    }
}

/// The sizes of one test (`TestSizes`, derive.h:43-47). `stages[0]` is the group itself.
#[derive(Clone, Debug, Default)]
pub struct TestSizes {
    pub group: GroupSize,
    /// The number of positions drawn for the group's list.
    pub t: u64,
    pub stages: Vec<Stage>,
}

/// What `derive` returns (`Derived`, derive.h:49-55).
#[derive(Clone, Debug, Default)]
pub struct Derived {
    pub set: Setting,
    /// A segment's group; `stages` stays empty.
    pub link: TestSizes,
    /// The last closing's message: the folded row and the carried row.
    pub last: TestSizes,
    pub table: TableSize,
    /// Not empty: why sizing failed; other fields may be incomplete.
    pub refused: String,
}

/// `setting_of()` (derive.h:57-65).
pub fn setting_of(p: &Parameters) -> Setting {
    let mut s = Setting::goldilocks();
    s.target = p.sec;
    s.samples = p.answers;
    s.salt_bytes = p.salt;
    for k in 0..5 {
        for i in 0..3 {
            s.work[k][i] = p.work[k][i];
        }
    }
    s
}

/// `shape_of()` (derive.h:67-73).
pub fn shape_of(name: &str, l: &GroupLine, k: u32, over_e: bool) -> GroupSize {
    GroupSize {
        name: String::from(name),
        k,
        h: 0,
        main: CodeSize {
            name: String::from(name),
            log_n: l.log_n,
            ell: 1u64 << l.log_ell,
            r: 0,
            over_e,
        },
        mask: CodeSize {
            name: format!("{} mask", name),
            log_n: l.mask_log_n,
            ell: 1u64 << l.mask_log_ell,
            r: 0,
            over_e: true,
        },
        ..GroupSize::default()
    }
}

/// `solve_group()` (derive.h:84-103). `draws(t)` is the number of drawn positions at which a main
/// row is opened when one list has `t`; a mask row is opened at one list. The last `x.t` is not
/// proved to be the smallest (the C++ comment says why).
pub fn solve_group<F: Fn(u64) -> u64>(
    s: &Setting,
    scope: Scope,
    load: &GroupLoad,
    draws: F,
    x: &mut TestSizes,
    why: &mut String,
) -> bool {
    let shape = x.group.clone();
    for _ in 0..32 {
        let mut g = shape.clone();
        g.main.r = tail_for(s, draws(x.t));
        g.mask.r = tail_for(s, x.t);
        if g.main.dim(s) > g.main.n() || g.mask.dim(s) > g.mask.n() {
            *why = format!("{}: message and random coordinates exceed the code's length", shape.name);
            return false;
        }
        let margin = Bound::from_real(&Real::two_to(-(s.target as i64) - 30));
        x.group = size_group(s, scope, &g, load);
        let serves = group_holds(s, scope, &x.group, load);
        let a = analysis_group(s, &x.group);
        let t = if serves {
            scope_positions(s, scope, &a.at.agree, &margin)
        } else if a.fault.is_some() {
            positions_from_below(s, scope, g, load, &margin)
        } else {
            0
        };
        if !serves && t <= x.t {
            *why = format!(
                "{}: {}",
                shape.name,
                a.fault.unwrap_or("no distance under its rule holds the group's rounds at the target")
            );
            return false;
        }
        if t == 0 {
            *why = format!("{}: no number of positions reaches the target", shape.name);
            return false;
        }
        if t <= x.t {
            return true;
        }
        x.t = t;
    }
    *why = format!("{}: positions and random coordinates do not settle", shape.name);
    false
}

/// `solve_test()` (derive.h:106-112): fills `x.stages` for the proximity test on `x.group`.
pub fn solve_test(s: &Setting, scope: Scope, l: &GroupLine, x: &mut TestSizes, why: &mut String) -> bool {
    let mut scratch = Plan::new(s.clone());
    scratch.begin_scope(scope);
    x.stages = crate::numbers::blocks::solve_stages(&mut scratch, &x.group, x.t, &l.stages);
    if scratch.refused() {
        *why = String::from(scratch.why());
    }
    !scratch.refused()
}

/// `derive_table()` (derive.h:115-123): fills `d.table` and its distances.
pub fn derive_table(p: &Parameters, d: &mut Derived) {
    let s = d.set.clone();
    let t = &mut d.table;
    t.code.name = String::from("table");
    t.code.log_n = p.table_log_n;
    t.code.ell = p.table_data;
    t.code.r = p.table_random;
    t.v = p.table_rows_log;
    t.answers = p.answers;
    if t.code.dim(&s) > t.code.n() {
        d.refused = String::from("table: data and random coordinates exceed the code's length");
        return;
    }
    if !size_recorded_table(&s, t, p.slots, p.block_log) {
        d.refused = String::from("table: no distance holds the fold point's round at the target");
    }
}

/// `derive()` (derive.h:125-149).
pub fn derive(p: &Parameters, f: &FrameShape) -> Derived {
    let mut d = Derived { set: setting_of(p), ..Derived::default() };
    let s = d.set.clone();
    let load_of = |g: &GroupSize, messages: u64, rows: u64| GroupLoad {
        cube_bits: stage_cube_bits(g),
        messages,
        batched_rows: rows,
    };
    let once = |t: u64| t;

    d.link.group = shape_of("link", &p.link, f.link_rows_log, false);
    d.link.group.slots = f.link_slots;
    let mut link_load = load_of(&d.link.group, f.link_messages as u64, f.link_batched_rows);
    link_load.cube_bits = core::cmp::max(link_load.cube_bits, f.link_cube_bits);
    if !solve_group(&s, Scope::Request, &link_load, once, &mut d.link, &mut d.refused) {
        return d;
    }
    // The last segment is closed into a message with the segments' codes, distance and t; it has at
    // most as many rows (not checked here), all over E, the extension field.
    d.last = d.link.clone();
    d.last.group.name = String::from("last");
    d.last.group.k = f.last_rows_log;
    d.last.group.slots = 1;
    d.last.group.main.over_e = true;
    if !solve_test(&s, Scope::Request, &p.link, &mut d.last, &mut d.refused) {
        return d;
    }
    derive_table(p, &mut d);
    d
}
