//! Sizing of LIN, the test on the committed table (`blocks/frame/lin_frame.h`).
//!
//! LIN proves one linear claim for each request of a batch with one fold of the table. This file
//! begins with its free parameters and the shape helpers; `lin_sized` (below, with the planner
//! pass) fixes the codes, positions, stages and plan.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::code::code::{hiding_positions, Code};
use crate::frame::derive::{shape_of, solve_test, FrameShape, TestSizes};
use crate::frame::parameters::{GroupLine, Parameters};
use crate::iop::context::{tree_sizes, OracleNotice};
use crate::iop::foldeq::{index_fault, IndexShape, E_DEGREE};
use crate::iop::iopp::{iopp_fault, iopp_stages, IoppStage};
use crate::iop::lin::{lin_fault, lin_message_omega, lin_message_u, lin_message_w, LinShape};
use crate::iop::relation::{Codes, OracleShape};
use crate::iop::send_pad::sample_cube;
use crate::numbers::blocks::{
    analysis_group, analysis_table, group_holds, plan_iopp, plan_lin_first, plan_lin_shared,
    plan_split, positions_from_below, pow2_at_least, scope_positions, size_group,
    stage_cube_bits, table_admitted, GroupLoad, GroupSize, LinSize, SampleSize, TableSize,
    TestedIn, TreeSize,
};
use crate::numbers::codes::{ceil_log2, tail_for};
use crate::numbers::plan::Plan;
use crate::numbers::real::{Bound, Real};
use crate::numbers::setting::{Scope, Setting};

/// LIN's parameters, without the table's sizes (`LinLines`, lin_frame.h:29-39).
#[derive(Clone, Debug)]
pub struct LinLines {
    /// A row of the table holds 2^k_lo columns of the matrix.
    pub k_lo: u32,
    pub matrix_rows: u64,
    pub folded: GroupLine,
    pub omega: GroupLine,
    pub own: GroupLine,
    /// The most requests in a batch.
    pub requests: u64,
    /// Of the request's oracle message whose entries mask its claim.
    pub input_mask_rows: usize,
    pub rows_high: bool,
    pub masks_ahead: bool,
    pub masks_ride: bool,
    /// The committer's one-time test: a batch of one at the one-time radius.
    pub one_time: bool,
    /// Columns of this table that LINK proofs to other tables open.
    pub columns_elsewhere: u64,
}

impl Default for LinLines {
    /// The C++ member defaults (lin_frame.h:30-39): the three flags are true, one request, one
    /// input mask row.
    fn default() -> Self {
        LinLines {
            k_lo: 0,
            matrix_rows: 0,
            folded: GroupLine::default(),
            omega: GroupLine::default(),
            own: GroupLine::default(),
            requests: 1,
            input_mask_rows: 1,
            rows_high: true,
            masks_ahead: true,
            masks_ride: true,
            one_time: false,
            columns_elsewhere: 0,
        }
    }
}

/// What LIN's chains are sized from (`LinSized`, lin_frame.h:52-60).
#[derive(Clone, Debug, Default)]
pub struct LinSized {
    pub lines: LinLines,
    pub s: LinShape,
    /// The request's mask message, as LIN's group expects it.
    pub input: OracleNotice,
    pub table: TableSize,
    pub folded: TestSizes,
    pub omega: TestSizes,
    pub own: TestSizes,
    /// Batches, counted when begun, that one stored table allows.
    pub batches: u64,
    /// Not empty: why these sizes are not valid.
    pub refused: String,
}

/// `lin_lines()` (lin_frame.h:43-50). `one_time`: from `once-folded`, `once-omega`, `once-own`.
pub fn lin_lines(p: &Parameters, f: &FrameShape, one_time: bool) -> LinLines {
    LinLines {
        k_lo: p.block_log.wrapping_sub(p.table_rows_log),
        matrix_rows: f.index_rows,
        folded: if one_time { p.once_folded.clone() } else { p.folded.clone() },
        omega: if one_time { p.once_omega.clone() } else { p.omega.clone() },
        own: if one_time { p.once_own.clone() } else { p.own.clone() },
        requests: if one_time { 1 } else { p.slots },
        one_time,
        ..LinLines::default()
    }
}

/// `lin_rows_of()` (lin_frame.h:62-65).
pub fn lin_rows_of(entries: u64, ell: u64, rows_high: bool) -> usize {
    let rows = (entries + ell - 1) / ell;
    (if rows_high { rows } else { pow2_at_least(rows) }) as usize
}

/// `lin_group_bits()` (lin_frame.h:69-73): the number of main and mask row variables of a group
/// whose members are these oracle messages.
pub fn lin_group_bits(members: &[&OracleShape]) -> (u32, u32) {
    let mut main = 0u64;
    let mut mask = 0u64;
    for m in members {
        main += if m.main_rows != 0 { pow2_at_least(m.main_rows as u64) } else { 0 };
        mask += if m.mask_rows != 0 { pow2_at_least(m.mask_rows as u64) } else { 0 };
    }
    let h = ceil_log2(mask);
    let k = core::cmp::max(core::cmp::max(ceil_log2(main), h), 1);
    (k, h)
}

/// One call of `lin_sized`'s local `size` lambda (lin_frame.h:151-166). `None`: the sizes are not
/// valid and `why` says why; `Some(serves)`: the group was sized and `serves` is `group_holds`.
#[allow(clippy::too_many_arguments)]
fn lin_size_group(
    s: &Setting,
    shape: &GroupSize,
    scope: Scope,
    main_draws: u64,
    mask_draws: u64,
    rows: u64,
    t: &mut TestSizes,
    margin: &Bound,
    why: &mut String,
) -> Option<bool> {
    let mut g = shape.clone();
    g.main.r = tail_for(s, main_draws);
    g.mask.r = tail_for(s, mask_draws);
    if g.main.dim(s) > g.main.n() || g.mask.dim(s) > g.mask.n() {
        *why = format!("{}: message and random coordinates exceed the code's length", shape.name);
        return None;
    }
    let load = GroupLoad { cube_bits: stage_cube_bits(&g), messages: 2, batched_rows: rows };
    t.group = size_group(s, scope, &g, &load);
    /* A group need not be valid yet: with too few random coordinates its main code can have a lower
       rate than its mask code. The main code alone then gives a number of positions that is not too
       large; validity is checked after the loop. */
    let serves = group_holds(s, scope, &t.group, &load);
    let more = if !serves {
        positions_from_below(s, scope, g, &load, margin)
    } else {
        scope_positions(s, scope, &analysis_group(s, &t.group).at.agree, margin)
    };
    if more == 0 {
        *why = format!(
            "{}: no distance under its rule, or no number of positions, holds the group's rounds at the target",
            shape.name
        );
        return None;
    }
    t.t = core::cmp::max(t.t, more);
    Some(serves)
}

/// `lin_sized()` (lin_frame.h:79-195). Adds LIN's missing codes to `codes`.
pub fn lin_sized(s: &Setting, l: &LinLines, table: &TableSize, codes: &mut Codes) -> LinSized {
    let mut x = LinSized { lines: l.clone(), ..LinSized::default() };
    let mut why = String::new();
    let shared = if l.one_time { Scope::Once } else { Scope::Shared };
    let request = if l.one_time { Scope::Once } else { Scope::Request };
    let split = l.folded.log_n != l.omega.log_n || l.folded.log_ell != l.omega.log_ell;
    if l.own.log_n != l.omega.log_n || l.own.log_ell != l.omega.log_ell {
        x.refused = String::from("own: a request's group has Omega's main code");
        return x;
    }
    if split && (l.folded.mask_log_n != l.omega.mask_log_n || l.folded.mask_log_ell != l.omega.mask_log_ell) {
        x.refused =
            String::from("omega: a split's mask message joins the folded row's group and Omega's: they have one mask code");
        return x;
    }
    let mut shape = LinShape::default();

    // ---- the table and its columns ----
    x.table = table.clone();
    if x.table.code.dim(s) > x.table.code.n() {
        x.refused = String::from("table: data and random coordinates exceed the code's length");
        return x;
    }
    let a = analysis_table(s, &x.table);
    if !table_admitted(&x.table, &a) {
        x.refused = String::from("table: the distances are not admitted");
        return x;
    }
    let agree = if l.one_time { a.once.agree.clone() } else { a.later.agree.clone() };
    shape.fold.columns = scope_positions(s, shared, &agree, &Bound::from_u64(0));
    if shape.fold.columns == 0 {
        // The C++ shape is written in place, so a refused `LinSized` shows what was filled.
        x.s = shape;
        x.refused = String::from("table: no number of columns reaches the target");
        return x;
    }

    // ---- shapes ----
    // They do not depend on the numbers of positions.
    let index = IndexShape {
        code: Code {
            log_n: x.table.code.log_n,
            ell: x.table.code.ell as usize,
            r: x.table.code.r as usize,
        },
        v: x.table.v,
        answers: s.samples,
        salt_bytes: s.salt_bytes as usize,
        distances: x.table.distances,
    };
    shape.k_lo = l.k_lo;
    shape.matrix_rows = l.matrix_rows;
    shape.fold.rows_high = l.rows_high;
    shape.omega_rows_high = l.rows_high;
    shape.w_rows_high = l.rows_high;
    shape.masks_ahead = l.masks_ahead;
    shape.choice.masks_ride = l.masks_ride;
    // The C++ shape is written in place: the index is set before its fault is checked.
    shape.fold.index = index;
    if let Some(f) = index_fault(&shape.fold.index) {
        x.s = shape;
        x.refused = format!("table: {}", f);
        return x;
    }
    /* A row's random coordinates (its random tail) hide a fixed number of columns in all. `spent`:
       the columns that the one-time test opens before the first batch, plus columns_elsewhere. In a
       leaf table LINK opens the same number as the one-time test. */
    let spent = scope_positions(s, Scope::Once, &a.once.agree, &Bound::from_u64(0))
        + l.columns_elsewhere;
    x.batches = if hiding_positions(&shape.fold.index.code) > spent {
        (hiding_positions(&shape.fold.index.code) - spent) / shape.fold.columns
    } else {
        0
    };
    let ell_u = 1u64 << l.folded.log_ell;
    let ell_o = 1u64 << l.omega.log_ell;
    let columns = 1u64 << shape.k_col();
    let message = |name: &str, main_rows: usize, mask_rows: usize| -> OracleShape {
        OracleShape {
            name: String::from(name),
            main_rows,
            main_deg: E_DEGREE as u32,
            mask_rows,
            answers: s.samples,
            ..OracleShape::default()
        }
    };
    shape.fold.u = message("the folded row", lin_rows_of(shape.fold.entries() + s.samples as u64, ell_u, l.rows_high), 0);
    shape.omega = message("Omega", lin_rows_of(l.matrix_rows + s.samples as u64, ell_o, l.rows_high), 0);
    // Each of the `Setting::samples` answers to an out-of-domain sample is masked by a pad: one
    // random entry at the end of the message's last mask row or, without mask rows, of its last main
    // row. W gets a mask row for its pads in two cases. Its main rows have fewer than `samples` free
    // places. Or `samples` is above 1 and rows_high is false: the end of the last main row then need
    // not be W's last entries.
    shape.w = message("W", lin_rows_of(columns, ell_o, l.rows_high), 0);
    if (shape.w.main_rows as u64) * ell_o - columns < s.samples as u64
        || (!l.rows_high && s.samples > 1)
    {
        shape.w.mask_rows = 1;
    }
    shape.shared_split = message("the mask of the split between Omega and the folded row", 0, 1);
    x.input = OracleNotice { shape: message("a request's masks", 0, l.input_mask_rows), leaf_class: 0 };

    // Groups are named after their parameter-file lines, so that a rejection names the line to fix.
    let line_name = |group: &str| -> String {
        format!("{}{}", if l.one_time { "once-" } else { "" }, group)
    };
    let folded_shape = {
        let (k, h) = if split {
            lin_group_bits(&[&shape.fold.u, &shape.shared_split])
        } else {
            lin_group_bits(&[&shape.fold.u, &shape.omega])
        };
        let mut g = shape_of(&line_name("folded"), &l.folded, k, true);
        g.h = h;
        g
    };
    let omega_shape = {
        let (k, h) = lin_group_bits(&[&shape.omega, &shape.shared_split]);
        let mut g = shape_of(&line_name("omega"), &l.omega, k, true);
        g.h = h;
        g
    };
    let own_shape = {
        let (k, h) = lin_group_bits(&[&x.input.shape, &shape.w, &shape.omega]);
        let mut g = shape_of(&line_name("own"), &l.own, k, true);
        g.h = h;
        g
    };

    // ---- positions and random coordinates, all groups together ----
    // A row needs random coordinates for all positions at which it is opened; they raise its code's
    // rate, and the rate fixes the number of positions. The groups share oracle messages, so all
    // are solved together, upward from 0.
    let margin = Bound::from_real(&Real::two_to(-(s.target as i64) - 30));
    let mut folded_serves = false;
    let mut omega_serves = false;
    let mut own_serves = false;
    for turn in 0u32.. {
        let a0 = x.folded.t;
        let b = x.omega.t;
        let c = x.own.t;
        let omega_draws = if split { b } else { a0 } + l.requests * c;
        let folded_rows = s.samples as u64 + shape.fold.columns + 1 + 2 * s.samples as u64;
        match lin_size_group(
            s,
            &folded_shape,
            shared,
            if split { a0 } else { omega_draws },
            if split { a0 + b } else { a0 },
            folded_rows,
            &mut x.folded,
            &margin,
            &mut why,
        ) {
            Some(v) => folded_serves = v,
            None => {
                x.s = shape.clone();
                x.refused = why;
                return x;
            }
        }
        if split {
            match lin_size_group(
                s,
                &omega_shape,
                shared,
                omega_draws,
                a0 + b,
                1 + 2 * s.samples as u64,
                &mut x.omega,
                &margin,
                &mut why,
            ) {
                Some(v) => omega_serves = v,
                None => {
                    x.refused = why;
                    return x;
                }
            }
        }
        match lin_size_group(
            s,
            &own_shape,
            request,
            omega_draws,
            c,
            2 + 3 * s.samples as u64,
            &mut x.own,
            &margin,
            &mut why,
        ) {
            Some(v) => own_serves = v,
            None => {
                x.s = shape.clone();
                x.refused = why;
                return x;
            }
        }
        if x.folded.t == a0 && x.omega.t == b && x.own.t == c {
            break;
        }
        if turn == 32 {
            x.s = shape.clone();
            x.refused = String::from("positions and random coordinates do not settle");
            return x;
        }
    }
    if !folded_serves {
        x.s = shape.clone();
        x.refused = format!(
            "{}: no distance under its rule holds the group's rounds at the target",
            x.folded.group.name
        );
        return x;
    }
    if split && !omega_serves {
        x.s = shape.clone();
        x.refused = format!(
            "{}: no distance under its rule holds the group's rounds at the target",
            x.omega.group.name
        );
        return x;
    }
    if !own_serves {
        x.s = shape.clone();
        x.refused = format!(
            "{}: no distance under its rule holds the group's rounds at the target",
            x.own.group.name
        );
        return x;
    }
    if !solve_test(s, shared, &l.folded, &mut x.folded, &mut why)
        || (split && !solve_test(s, shared, &l.omega, &mut x.omega, &mut why))
        || !solve_test(s, request, &l.own, &mut x.own, &mut why)
    {
        x.s = shape.clone();
        x.refused = why;
        return x;
    }

    // ---- codes and stages ----
    shape.test_u = iopp_stages(&x.folded.stages, codes);
    if split {
        shape.test_omega = iopp_stages(&x.omega.stages, codes);
    }
    shape.test_own = iopp_stages(&x.own.stages, codes);
    shape.fold.u.code = shape.test_u[0].code;
    shape.omega.code = shape.test_own[0].code;
    shape.w.code = shape.test_own[0].code;
    shape.shared_mask_code = shape.test_u[0].mask_code;
    shape.shared_split.mask_code = shape.test_u[0].mask_code;
    shape.own_mask_code = shape.test_own[0].mask_code;
    shape.w.mask_code = shape.test_own[0].mask_code;
    x.input.shape.mask_code = shape.test_own[0].mask_code;
    let omega_code = if split { shape.test_omega[0].code } else { shape.omega.code };
    assert!(
        shape.shared_split_needed() == split && (!split || omega_code == shape.omega.code),
        "lin_frame: Omega has not one code in all its groups"
    );
    if let Some(f) = lin_fault(codes, &shape) {
        x.s = shape.clone();
        x.refused = format!("LIN: {}", f);
        return x;
    }
    let mut stage = 0usize;
    for test in [&shape.test_u, &shape.test_omega, &shape.test_own] {
        if !test.is_empty() {
            if let Some(f) = iopp_fault(codes, test, s.samples, &mut stage) {
                x.s = shape.clone();
                x.refused = format!("a proximity test of LIN: {}", f);
                return x;
            }
        }
    }
    x.s = shape;
    x
}

// ---- LIN's share of the three chains' Plans ----
// blocks/iop/lin.h defines each prover message's oracle messages (lin_message_w() etc.).

/// `lin_size_of()` (lin_frame.h:200-214).
pub fn lin_size_of(codes: &Codes, x: &LinSized) -> LinSize {
    let shape = &x.s;
    // List sizes come from stages[0].g, from which plan_iopp() computes the test's round errors;
    // TestSizes::group is an equal copy.
    let around_omega =
        if shape.shared_split_needed() { &x.omega.stages[0].g } else { &x.folded.stages[0].g };
    let mut z = LinSize::new(
        SampleSize { cube_bits: sample_cube(codes, &shape.w).bits, groups: TestedIn::new(&x.own.stages[0].g) },
        SampleSize {
            cube_bits: sample_cube(codes, &shape.fold.u).bits,
            groups: TestedIn::new(&x.folded.stages[0].g),
        },
        SampleSize {
            cube_bits: sample_cube(codes, &shape.omega).bits,
            groups: TestedIn::with_two(around_omega, &x.own.stages[0].g),
        },
    );
    z.instances = x.lines.requests;
    z.one_time = x.lines.one_time;
    z.k_lo = shape.k_lo;
    z.rows_log = shape.k_row();
    if shape.shared_split_needed() {
        z.beside_omega.push(SampleSize {
            cube_bits: sample_cube(codes, &shape.shared_split).bits,
            groups: TestedIn::with_two(&x.folded.stages[0].g, &x.omega.stages[0].g),
        });
    }
    z.roots_w = lay_roots(codes, &lin_message_w(shape));
    z.roots_u = lay_roots(codes, &lin_message_u(shape));
    z.roots_omega = lay_roots(codes, &lin_message_omega(shape));
    z
}

fn lay_roots(codes: &Codes, sent: &[OracleNotice]) -> u32 {
    crate::iop::context::lay_trees(codes, sent, 0).shapes.len() as u32
}

/// `lin_plan_first()` (lin_frame.h:217): on the request's first chain, before its seal.
pub fn lin_plan_first(p: &mut Plan, codes: &Codes, x: &LinSized) {
    plan_lin_first(p, "table", &lin_size_of(codes, x));
}

/// `lin_require_sized()` (lin_frame.h:221-224): ends the process unless `solved`, from which the
/// plan computes a proximity test's errors, matches the shape's `stages` under `codes`.
pub fn lin_require_sized(codes: &Codes, stages: &[IoppStage], solved: &[crate::numbers::blocks::Stage]) {
    let fault = crate::iop::iopp::iopp_sized_fault(codes, stages, solved);
    assert!(fault.is_none(), "{}", fault.unwrap_or(""));
}

/// `lin_plan_shared()` (lin_frame.h:227-245): on the shared chain, from its first round to before
/// its seal. `table_tree`: how the table's columns are hashed. `last` numbers marked trees
/// (`OneList`), as `OneList::mark` expects; the C++ header keeps that counter in a static.
pub fn lin_plan_shared(
    p: &mut Plan,
    codes: &Codes,
    x: &LinSized,
    table_tree: &TreeSize,
    last: &mut u64,
) {
    let shape = &x.s;
    let nu = plan_lin_shared(p, "table", &x.table, &lin_size_of(codes, x), table_tree);
    if !p.refused() {
        assert_eq!(nu, shape.fold.columns, "lin_frame: the plan draws another number of columns");
    }
    let mut trees = tree_sizes(codes, &lin_message_u(shape), last);
    let with_omega = tree_sizes(codes, &lin_message_omega(shape), last);
    let samples = p.set.samples as u64;
    if shape.shared_split_needed() {
        plan_split(p, "Omega against the folded row");
        trees.push(with_omega[1].clone());
        lin_require_sized(codes, &shape.test_u, &x.folded.stages);
        lin_require_sized(codes, &shape.test_omega, &x.omega.stages);
        plan_iopp(
            p,
            "folded row",
            &x.folded.stages,
            &trees,
            shape.fold.index.answers as u64 + nu + 1 + 2 * samples,
            if shape.masks_ahead { 0 } else { 1 },
            shape.choice.masks_ride,
            last,
        );
        plan_iopp(p, "Omega", &x.omega.stages, &with_omega, 1 + 2 * samples, 1, shape.choice.masks_ride, last);
    } else {
        trees.push(with_omega[0].clone());
        lin_require_sized(codes, &shape.test_u, &x.folded.stages);
        plan_iopp(
            p,
            "folded row and Omega",
            &x.folded.stages,
            &trees,
            shape.fold.index.answers as u64 + nu + 1 + 2 * samples,
            if shape.masks_ahead { 0 } else { 1 },
            shape.choice.masks_ride,
            last,
        );
    }
}

/// `lin_plan_second()` (lin_frame.h:247-256): on the request's second chain. `input_trees`: the
/// trees that hold the request's mask message.
pub fn lin_plan_second(
    p: &mut Plan,
    codes: &Codes,
    x: &LinSized,
    input_trees: &[TreeSize],
    last: &mut u64,
) {
    let shape = &x.s;
    let mut trees: Vec<TreeSize> = input_trees.to_vec();
    for t in tree_sizes(codes, &lin_message_w(shape), last) {
        trees.push(t);
    }
    let mut omega = tree_sizes(codes, &lin_message_omega(shape), last)[0].clone();
    // from the shared chain, opened by every request: `plan_open` rejects the plan if `one_list`
    // marks the tree as having a mask for one list of positions only
    omega.from_another_chain = true;
    trees.push(omega);
    lin_require_sized(codes, &shape.test_own, &x.own.stages);
    plan_iopp(
        p,
        "a request's own test",
        &x.own.stages,
        &trees,
        2 + 3 * (p.set.samples as u64),
        if shape.masks_ahead { 0 } else { 1 },
        shape.choice.masks_ride,
        last,
    );
}
