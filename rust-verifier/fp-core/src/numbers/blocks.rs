//! Group and table sizes, their analyses, the stage/table sizing that the planners call, and the
//! planners themselves (`blocks/numbers/blocks.h`).
//!
//! The analysis and sizing half: `GroupSize` and its `Analysis`, `GroupLoad`, the group and table
//! analyses, `size_group`, `scope_positions`, `solve_stages` and `size_recorded_table`. The second
//! half appends rounds and messages to a `Plan`: `plan_send`, `plan_bat`, `plan_psc`, `plan_fold`,
//! `plan_iopp`, `plan_record`, `plan_lin_shared`, `plan_link` and the rest, with the file and tree
//! helpers of `MayLay`.

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

pub use crate::frame::parameters::StageChoice;
use crate::numbers::codes::{
    at_distance, at_distance_code, ceil_log2, field_error, field_error_nonzero, johnson,
    johnson_code, mca_error, positions, powers_error, repeated, sample_error, sample_error_default,
    tail_for, CodeSize, Proximity, Radius,
};
use crate::numbers::plan::{
    MessageKind, Plan, PlanRound, Priced, PricedCode, PricedGroup, PricedTable, TableDistances,
    TableTest,
};
use crate::numbers::real::{surely_le, Big, Bound, Dir, Real};
use crate::numbers::round_names::*;
use crate::numbers::setting::{CountSource, ErrorKind, RoundKind, Scope, Setting};

/// The default cap of `largest_m` (`u64 limit = (u64)1 << 40`, codes.h:269).
pub const LARGEST_M_LIMIT: u64 = 1 << 40;

// ---------------------------------------------------------------------------------------------------------------------
// Groups

/// A group: 2^k main rows under one code and 2^h mask rows under the mask code (`GroupSize`,
/// blocks.h:46-56). `slots > 1`: each main row stands for `slots` rows folded side by side.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GroupSize {
    pub name: String,
    pub main: CodeSize,
    pub mask: CodeSize,
    pub k: u32,
    pub h: u32,
    pub slots: u64,
    /// The rule that fixes the distance (`JOHNSON` by default).
    pub rule: Radius,
    /// JOHNSON: the theorem's integer m; AT: the distance, in positions of the main code.
    pub m: u64,
}

impl Default for GroupSize {
    fn default() -> Self {
        GroupSize {
            name: String::new(),
            main: CodeSize::default(),
            mask: CodeSize::default(),
            k: 0,
            h: 0,
            slots: 1,
            rule: Radius::Johnson,
            m: 0,
        }
    }
}

impl GroupSize {
    pub fn has_mask(&self) -> bool {
        self.mask.ell != 0
    }
}

/// What `analysis` derives from a group and the setting (`Analysis`, blocks.h:61-68).
#[derive(Clone, Debug)]
pub struct Analysis {
    /// The main code at the group's distance.
    pub at: Proximity,
    /// The mask code at the same distance; not read for a group without mask rows.
    pub mask_at: Proximity,
    /// List size of the main and mask rows together.
    pub list: Big,
    /// `shape_fault`'s reason, if the shape is why the analysis is bad.
    pub fault: Option<&'static str>,
    pub with_mask: bool,
}

impl Default for Analysis {
    fn default() -> Self {
        Analysis {
            at: Proximity::default(),
            mask_at: Proximity::default(),
            list: Big::from_u64(1),
            fault: None,
            with_mask: false,
        }
    }
}

impl Analysis {
    pub fn bad(&self) -> bool {
        self.at.bad() || (self.with_mask && self.mask_at.bad())
    }
}

/// The public numbers of a code as a plan records them (`priced(const CodeSize&)`, blocks.h:78-82).
pub fn priced_code(c: &CodeSize) -> PricedCode {
    PricedCode { log_n: c.log_n, ell: c.ell, r: c.r }
}

/// What a plan records about a group (`priced(const GroupSize&)`, blocks.h:83-91).
pub fn priced_group(g: &GroupSize) -> PricedGroup {
    let mut x = PricedGroup {
        main: priced_code(&g.main),
        k: g.k,
        h: g.h,
        slots: g.slots,
        said: true,
        rule: g.rule as u32,
        m: g.m,
        ..PricedGroup::default()
    };
    if g.has_mask() {
        x.mask = priced_code(&g.mask);
    }
    x
}

/// The same for a round that draws positions on a group's rows (`priced_codes`, blocks.h:96-100).
pub fn priced_codes(g: &GroupSize) -> PricedGroup {
    let mut x = priced_group(g);
    x.k = 0;
    x.h = 0;
    x.slots = 1;
    x
}

/// True if the mask code has the larger rate (`mask_rules`, blocks.h:206).
pub fn mask_rules(s: &Setting, g: &GroupSize) -> bool {
    g.has_mask()
        && (g.mask.k(s) as u128) * (g.main.n() as u128) > (g.main.k(s) as u128) * (g.mask.n() as u128)
}

/// Null, or why the blocks do not allow the shape (`shape_fault`, blocks.h:108-114).
pub fn shape_fault(s: &Setting, g: &GroupSize) -> Option<&'static str> {
    if !g.has_mask() {
        return if g.h != 0 { Some("mask rows without a mask code") } else { None };
    }
    if g.mask.log_n > g.main.log_n {
        return Some("the mask code is longer than the main code");
    }
    if g.h > g.k {
        return Some("more row variables for the mask rows than for the main rows");
    }
    if g.k > 0 && g.h == 0 && mask_rules(s, g) {
        return Some("a single mask row beside rows that are folded has a code of a larger rate than theirs: lengthen the mask code");
    }
    None
}

/// The analysis of a group whose main code is at `at` (`analysis_at`, blocks.h:117-149).
pub fn analysis_at(s: &Setting, g: &GroupSize, at: &Proximity) -> Analysis {
    let mut a = Analysis {
        at: at.clone(),
        list: at.list.clone(),
        with_mask: g.has_mask(),
        ..Analysis::default()
    };
    if let Some(fault) = shape_fault(s, g) {
        a.fault = Some(fault);
        a.at.count = Bound::failed();
    }
    if g.has_mask() {
        a.mask_at = at_distance(&repeated(s, &g.mask, g.main.log_n), &at.agree);
        if Big::cmp(&a.list, &a.mask_at.list) == Ordering::Less {
            a.list = a.mask_at.list.clone();
        }
        if a.mask_at.source != CountSource::Third {
            a.mask_at.count = a.mask_at.count.clone() + Bound::from_big(&a.mask_at.list);
        }
    }
    a
}

/// The error of FOLD's round `j = 1..k` (`fold_round_error`, blocks.h:154-158).
pub fn fold_round_error(s: &Setting, g: &GroupSize, a: &Analysis, j: u32) -> Bound {
    let mut e = mca_error(s, &a.at) + Bound::from_big(&a.list) * field_error(s, 2);
    if g.has_mask() && j <= g.h {
        e = e + Bound::from_u64(2) * mca_error(s, &a.mask_at);
    }
    e
}

/// The error of BASE's first round, for a group of single rows (`base_error`, blocks.h:163-167).
pub fn base_error(s: &Setting, g: &GroupSize, a: &Analysis) -> Bound {
    let mut e = mca_error(s, &a.at) + Bound::from_big(&a.list) * field_error(s, 1);
    if g.has_mask() {
        e = e + mca_error(s, &a.mask_at);
    }
    e
}

/// What `group_holds` assumes of rounds outside FOLD and BASE (`GroupLoad`, blocks.h:175-179).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GroupLoad {
    pub cube_bits: u32,
    pub messages: u64,
    pub batched_rows: u64,
}

impl Default for GroupLoad {
    fn default() -> Self {
        GroupLoad { cube_bits: 40, messages: 4, batched_rows: 1 << 20 }
    }
}

/// The largest error that meets the target with `w` bits of proof of work (`goal_of`,
/// blocks.h:186-189). In the scope REQUEST it is divided by `Setting::instances`.
pub fn goal_of(s: &Setting, why: ErrorKind, scope: Scope) -> Real {
    let g = Real::two_to(s.work_of(why, scope) as i64 - s.target as i64);
    if scope == Scope::Request {
        Real::div(&g, &Real::from_u64(s.instances), Dir::Down)
    } else {
        g
    }
}

/// True if the rounds whose error depends on the group's distance, except the draws of positions,
/// meet the target under `load` (`group_holds`, blocks.h:193-200).
pub fn group_holds(s: &Setting, scope: Scope, g: &GroupSize, load: &GroupLoad) -> bool {
    let a = analysis_group(s, g);
    if a.bad() {
        return false;
    }
    let worst = if g.k != 0 {
        fold_round_error(s, g, &a, 1)
    } else {
        base_error(s, g, &a)
    };
    Real::cmp(&worst.error(), &goal_of(s, ErrorKind::Closeness, scope)) != Ordering::Greater
        && Real::cmp(
            &(Bound::from_big(&Big::from_u64(load.messages))
                * sample_error_default(s, &a.list, load.cube_bits))
                .error(),
            &goal_of(s, ErrorKind::Sample, scope),
        ) != Ordering::Greater
        && Real::cmp(
            &(Bound::from_big(&a.list)
                * (powers_error(s, load.batched_rows) + field_error(s, 1)))
                .error(),
            &goal_of(s, ErrorKind::Field, scope),
        ) != Ordering::Greater
}

/// The group under the rule JOHNSON with the integer m (`group_of_m`, blocks.h:208-212).
pub fn group_of_m(shape: &GroupSize, m: u64) -> GroupSize {
    let mut g = shape.clone();
    g.m = m;
    g.rule = Radius::Johnson;
    g
}

/// The analysis under JOHNSON at `m`, for the code with the larger rate (`analysis_of_m`,
/// blocks.h:213-220).
pub fn analysis_of_m(s: &Setting, g: &GroupSize) -> Analysis {
    if !mask_rules(s, g) {
        return analysis_at(s, g, &johnson_code(s, &g.main, g.m));
    }
    let mut z = johnson(&repeated(s, &g.mask, g.main.log_n), g.m);
    let mut a = analysis_at(s, g, &at_distance_code(s, &g.main, &z.agree));
    z.count = z.count.clone() + Bound::from_big(&z.list);
    a.mask_at = z;
    a
}

/// The group at the largest m that `largest_m` finds with `group_holds` true (`size_group`,
/// blocks.h:224-227). No m: `m = 0` and a bad analysis.
pub fn size_group(s: &Setting, scope: Scope, shape: &GroupSize, load: &GroupLoad) -> GroupSize {
    let m = crate::numbers::codes::largest_m(
        |m| group_holds(s, scope, &group_of_m(shape, m), load),
        LARGEST_M_LIMIT,
    );
    group_of_m(shape, m)
}

/// The group at a distance that the caller names, in whole positions (`group_at`, blocks.h:230-234).
pub fn group_at(shape: &GroupSize, positions: u64) -> GroupSize {
    let mut g = shape.clone();
    g.m = positions;
    g.rule = Radius::At;
    g
}

/// The analysis of a group under its rule (`analysis(const Setting&, const GroupSize&)`,
/// blocks.h:241-247).
pub fn analysis_group(s: &Setting, g: &GroupSize) -> Analysis {
    match g.rule {
        Radius::Johnson => analysis_of_m(s, g),
        Radius::At => analysis_at(
            s,
            g,
            &at_distance_code(
                s,
                &g.main,
                &(Bound::from_u64(1) - Bound::ratio(&Big::from_u64(g.m), &Big::from_u64(g.main.n()))),
            ),
        ),
    }
}

/// The group's analysis; the plan is rejected if it is bad (`analysis(Plan&, ..)`,
/// blocks.h:249-253).
pub fn analysis_group_in_plan(p: &mut Plan, where_: &str, g: &GroupSize) -> Analysis {
    let a = analysis_group(&p.set, g);
    if a.bad() {
        p.refuse(&format!(
            "{}: {}",
            where_,
            a.fault.unwrap_or("the group's codes have no admissible distance under its rule")
        ));
    }
    a
}

/// The smallest number of positions for a draw in `scope` (`scope_positions`, blocks.h:470-474).
/// 0: none reaches the target.
pub fn scope_positions(s: &Setting, scope: Scope, agree: &Bound, extra: &Bound) -> u64 {
    let w = s.work_of(ErrorKind::Query, scope);
    positions(
        agree,
        if s.target > w { s.target - w } else { 0 },
        extra,
        if scope == Scope::Request { s.instances } else { 1 },
    )
}

/// As `scope_positions`, with no other term (`blocks.h:475`).
pub fn scope_positions_default(s: &Setting, scope: Scope, agree: &Bound) -> u64 {
    scope_positions(s, scope, agree, &Bound::from_u64(0))
}

/// `scope_positions` under the plan's setting and scope (`plan_positions`, blocks.h:476-478).
pub fn plan_positions(p: &Plan, agree: &Bound, extra: &Bound) -> u64 {
    scope_positions(&p.set, p.scope(), agree, extra)
}

/// As `plan_positions`, with no other term.
pub fn plan_positions_default(p: &Plan, agree: &Bound) -> u64 {
    plan_positions(p, agree, &Bound::from_u64(0))
}

/// For the iteration from below in `solve_stages` (`positions_from_below`, blocks.h:260-264).
/// 0: not even the main code alone meets the target.
pub fn positions_from_below(
    s: &Setting,
    scope: Scope,
    mut shape: GroupSize,
    load: &GroupLoad,
    extra: &Bound,
) -> u64 {
    shape.mask = CodeSize::default();
    shape.h = 0;
    let g = size_group(s, scope, &shape, load);
    if group_holds(s, scope, &g, load) {
        scope_positions(s, scope, &analysis_group(s, &g).at.agree, extra)
    } else {
        0
    }
}

/// On what the group's proximity terms rest: the weaker of its two codes' sources
/// (`weakest_source`, blocks.h:266-268).
pub fn weakest_source(a: &Analysis) -> CountSource {
    if a.with_mask && source_rank(a.mask_at.source) > source_rank(a.at.source) {
        a.mask_at.source
    } else {
        a.at.source
    }
}

fn source_rank(c: CountSource) -> u8 {
    match c {
        CountSource::Third => 0,
        CountSource::Johnson => 1,
    }
}

// ---------------------------------------------------------------------------------------------------------------------
// Trees and openings

/// Marks a tree with an oracle message that may be read at one list of positions only (`OneList`,
/// blocks.h:282-292).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OneList {
    pub yes: bool,
    pub number: u64,
}

impl OneList {
    /// `OneList::operator=(bool)` (blocks.h:285-290). The C++ numbers marked trees in a
    /// process-wide static; file-scope state is forbidden here, so the caller passes the counter
    /// and this gives the tree the next number, as `++last` does there.
    pub fn mark(&mut self, yes: bool, last: &mut u64) {
        self.yes = yes;
        if yes && self.number == 0 {
            *last += 1;
            self.number = *last;
        }
    }
}

/// The sizes of one Merkle tree (`TreeSize`, blocks.h:299-305).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TreeSize {
    pub name: String,
    pub log_n: u32,
    pub leaf_bytes: u64,
    pub one_list: OneList,
    pub from_another_chain: bool,
}

/// How many of 2^log_n positions do t independent uniform draws hit, on average
/// (`expected_distinct`, blocks.h:308-311).
pub fn expected_distinct(log_n: u32, t: u64) -> f64 {
    let n = libm::ldexp(1.0, log_n as i32);
    -n * libm::expm1(t as f64 * libm::log1p(-1.0 / n))
}

/// Sibling digests that a pruned opening of t positions needs, at most (`path_digests_most`,
/// blocks.h:322-328).
pub fn path_digests_most(log_n: u32, t: u64) -> u64 {
    if t == 0 || log_n == 0 {
        return 0;
    }
    let t = core::cmp::min(t, 1u64 << (log_n - 1));
    let mut a = 0u32;
    while (2u64 << a) <= t {
        a += 1;
    }
    t * (log_n as u64 - a as u64 - 1) + (2u64 << a) - t
}

/// The average over t independent uniform draws (`path_digests_expected`, blocks.h:329-336).
pub fn path_digests_expected(log_n: u32, t: u64) -> f64 {
    let mut d = 0.0;
    for j in 1..=log_n {
        let n = libm::ldexp(1.0, j as i32);
        let second = if j == 1 {
            0.0
        } else {
            libm::exp(t as f64 * libm::log1p(-2.0 / n))
        };
        d += n * (libm::exp(t as f64 * libm::log1p(-1.0 / n)) - second);
    }
    d
}

// ---------------------------------------------------------------------------------------------------------------------
// Which rows are tested where

/// The groups in which some rows are tested (`TestedIn`, blocks.h:494-508).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TestedIn {
    groups_: Vec<GroupSize>,
}

impl TestedIn {
    pub fn new(g: &GroupSize) -> Self {
        TestedIn { groups_: vec![g.clone()] }
    }

    pub fn with_two(g: &GroupSize, h: &GroupSize) -> Self {
        TestedIn { groups_: vec![g.clone(), h.clone()] }
    }

    pub fn groups(&self) -> &[GroupSize] {
        &self.groups_
    }
}

/// The empty case: a list size of 1 that nothing checks (`no_sized_group`, blocks.h:508).
pub fn no_sized_group() -> TestedIn {
    TestedIn::default()
}

// ---------------------------------------------------------------------------------------------------------------------
// The stages of a proximity test

/// The sizes of the stages (`Stage`, blocks.h:840-844).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stage {
    pub g: GroupSize,
    /// Positions at which this stage's rows are opened.
    pub t: u64,
    /// Entries that fill the mask rows of this stage, the pad among them.
    pub r_ood: u64,
}

/// The smallest power of two at least `x` (`pow2_at_least`, blocks.h:845).
pub fn pow2_at_least(x: u64) -> u64 {
    1u64 << ceil_log2(x)
}

/// The largest number of variables of a sample's point on one of the stage's oracle messages
/// (`stage_cube_bits`, blocks.h:847-850).
pub fn stage_cube_bits(g: &GroupSize) -> u32 {
    let a = g.k + ceil_log2(g.main.ell);
    let b = if g.has_mask() { g.h + ceil_log2(g.mask.ell) } else { 0 };
    if g.has_mask() {
        core::cmp::max(a, b) + 1
    } else {
        a
    }
}

/// Solves the sizes of a proximity test's stages (`solve_stages`, blocks.h:856-911). Stage 1 is
/// `first`; a further stage's choice gives the rest. Adds nothing to `p`: it reads the setting and
/// scope, and rejects `p` if a choice cannot be met; the result may then lack stages.
pub fn solve_stages(
    p: &mut Plan,
    first: &GroupSize,
    first_t: u64,
    choice: &[StageChoice],
) -> Vec<Stage> {
    let s = p.set.clone();
    let scope = p.scope();
    let mut st = vec![Stage { g: first.clone(), t: first_t, r_ood: 0 }];
    if choice.is_empty() || first.k == 0 {
        p.refuse(&format!("{}: a proximity test folds at its first stage and has a last stage", first.name));
    }
    for (i, c) in choice.iter().enumerate() {
        let o = st.last().unwrap().g.clone();
        let mut n = Stage::default();
        n.g.name = format!("{}, stage {}", first.name, i + 2);
        if c.h > c.k || c.k > 32 || (if i + 1 == choice.len() { c.k != 0 } else { c.k == 0 }) {
            p.refuse(&format!(
                "{}: a middle stage has 1 <= k and h <= k, the last stage k = h = 0",
                n.g.name
            ));
            break;
        }
        n.g.k = c.k;
        n.g.h = c.h;
        n.g.main.name = n.g.name.clone();
        n.g.main.log_n = c.log_n;
        n.g.main.over_e = true;
        n.g.mask.name = format!("{} mask", n.g.name);
        n.g.mask.log_n = c.mask_log_n;
        n.g.mask.over_e = true;
        if o.main.ell.wrapping_mul(o.slots) % (1u64 << c.k) != 0 {
            p.refuse(&format!("{}: the folded row cannot be cut into 2^k rows", n.g.name));
            break;
        }
        n.g.main.ell = (o.main.ell.wrapping_mul(o.slots)) >> c.k;
        let carried = 2u64
            .wrapping_mul(o.mask.ell)
            .wrapping_add(o.main.r.wrapping_mul(o.slots))
            .wrapping_add(2u64.wrapping_mul(o.mask.r));
        let own_fold = if c.k != 0 { 2 * c.k as u64 + 1 - c.h as u64 } else { 1 };
        n.g.mask.ell = core::cmp::max(
            pow2_at_least(
                (carried
                    .wrapping_add(s.samples as u64)
                    .wrapping_add(1u64 << c.h)
                    .wrapping_sub(1))
                    >> c.h,
            ),
            pow2_at_least(own_fold),
        );
        n.r_ood = (n.g.mask.ell << c.h).wrapping_sub(carried);
        let mut t = 0u64;
        let mut turn = 0u32;
        loop {
            if turn == 32 {
                p.refuse(&format!("{}: positions and random coordinates do not settle", n.g.name));
                break;
            }
            turn += 1;
            n.g.main.r = tail_for(&s, t);
            n.g.mask.r = tail_for(&s, t);
            if n.g.main.dim(&s) > n.g.main.n() || n.g.mask.dim(&s) > n.g.mask.n() {
                p.refuse(&format!("{}: message and randomness do not fit the code's length", n.g.name));
                break;
            }
            let load = GroupLoad {
                cube_bits: stage_cube_bits(&n.g),
                messages: 1,
                // assumed: CS into this stage batches three claims for each position of the stage
                // before
                batched_rows: 4 + 3 * core::cmp::max(o.main.r, 1024),
            };
            let margin = Bound::from_real(&Real::two_to(-(s.target as i64) - 30));
            let shape = n.g.clone();
            n.g = size_group(&s, scope, &shape, &load);
            let serves = group_holds(&s, scope, &n.g, &load);
            let a = analysis_group(&s, &n.g);
            let t2 = if serves {
                plan_positions(p, &a.at.agree, &margin)
            } else if a.fault.is_some() {
                positions_from_below(&s, scope, shape, &load, &margin)
            } else {
                0
            };
            if !serves && t2 <= t {
                p.refuse(&format!(
                    "{}: {}",
                    n.g.name,
                    a.fault.unwrap_or("no distance under its rule holds the stage's rounds at the target")
                ));
                break;
            }
            if t2 <= t {
                break;
            }
            t = t2;
        }
        n.t = t;
        st.push(n);
    }
    st
}

// ---------------------------------------------------------------------------------------------------------------------
// The committed table: RECORD, LIN, LINK

/// The committed table: 2^v rows over F under one code (`TableSize`, blocks.h:967-975).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableSize {
    pub code: CodeSize,
    pub v: u32,
    /// Answers for each row, each with a seed and pads of its own.
    pub answers: u32,
    /// The caller's choice: the two distances (`TableDistances`, plan.h).
    pub distances: TableDistances,
}

impl Default for TableSize {
    fn default() -> Self {
        TableSize { code: CodeSize::default(), v: 0, answers: 1, distances: TableDistances::default() }
    }
}

/// A result, like `Analysis`: no struct stores it (`TableAnalysis`, blocks.h:976-979).
#[derive(Clone, Debug)]
pub struct TableAnalysis {
    /// The code at delta_M.
    pub once: Proximity,
    /// The code at delta'.
    pub later: Proximity,
}

impl Default for TableAnalysis {
    fn default() -> Self {
        TableAnalysis { once: Proximity::default(), later: Proximity::default() }
    }
}

/// The table's two distances and their codes' counts and list sizes (`analysis(const Setting&,
/// const TableSize&)`, blocks.h:980-990).
pub fn analysis_table(s: &Setting, t: &TableSize) -> TableAnalysis {
    if t.distances.m_once != 0 {
        return TableAnalysis {
            once: johnson_code(s, &t.code, t.distances.m_once),
            later: johnson_code(s, &t.code, t.distances.m_later),
        };
    }
    let n = Big::from_u64(t.code.n());
    let share = Bound::ratio(&Big::from_u64(t.distances.radius), &n);
    TableAnalysis {
        once: at_distance_code(s, &t.code, &(Bound::from_u64(1) - share)),
        later: at_distance_code(
            s,
            &t.code,
            &(Bound::from_u64(1) - Bound::ratio(&Big::from_u64(t.distances.later_radius), &n)),
        ),
    }
}

/// What a plan records of the table (`priced(const TableSize&, TableTest)`, blocks.h:993-999).
pub fn priced_table(t: &TableSize, test: TableTest) -> PricedTable {
    PricedTable {
        code: priced_code(&t.code),
        v: t.v,
        answers: t.answers,
        distances: t.distances,
        said: true,
        test,
    }
}

/// A condition on the distances (`table_admitted(const TableSize&, const TableAnalysis&)`,
/// blocks.h:1009-1013).
pub fn table_admitted(t: &TableSize, a: &TableAnalysis) -> bool {
    if a.once.bad() {
        return false;
    }
    if a.later.bad() || t.answers == 0 {
        return false;
    }
    if a.once.from_m && a.later.from_m {
        a.later.m <= a.once.m
    } else {
        surely_le(&a.later.delta, &a.once.delta)
    }
}

/// `table_admitted` from the setting (`blocks.h:1014`).
pub fn table_admitted_of(s: &Setting, t: &TableSize) -> bool {
    table_admitted(t, &analysis_table(s, t))
}

/// The table's analysis; the plan is rejected unless `table_admitted` (`analysis(Plan&, ..)`,
/// blocks.h:1016-1020).
pub fn analysis_table_in_plan(p: &mut Plan, where_: &str, t: &TableSize) -> TableAnalysis {
    let a = analysis_table(&p.set, t);
    if !table_admitted(t, &a) {
        p.refuse(&format!("{}: the table's distances are not admitted", where_));
    }
    a
}

/// The error of a fold of all 2^v rows by equality weights in one message (`table_fold_error`,
/// blocks.h:1023-1027).
pub fn table_fold_error(s: &Setting, t: &TableSize, at: &Proximity) -> Bound {
    let mut e = Bound::from_u64(0);
    for _ in 1..=t.v {
        e = e + mca_error(s, at);
    }
    e + Bound::from_big(&at.list) * field_error(s, t.v as u64)
}

/// Derives the table's two distances (`size_recorded_table`, blocks.h:1037-1051). Returns false if
/// no distance suffices.
pub fn size_recorded_table(
    s: &Setting,
    t: &mut TableSize,
    requests: u64,
    point_variables: u32,
) -> bool {
    let m_once;
    let m_later;
    {
        let sized = |scope: Scope, sharing: u64, with_record: bool| -> u64 {
            crate::numbers::codes::largest_m(
                |m| {
                    let x = johnson_code(s, &t.code, m);
                    if x.bad() {
                        return false;
                    }
                    let point = Bound::from_big(&Big::from_u64(sharing))
                        * field_error(s, point_variables as u64)
                        + Bound::from_u64(2) * table_fold_error(s, t, &x);
                    Real::cmp(&point.error(), &goal_of(s, ErrorKind::Closeness, scope))
                        != Ordering::Greater
                        && (!with_record
                            || Real::cmp(
                                &sample_error(
                                    s,
                                    &x.list,
                                    ceil_log2(t.code.ell),
                                    t.answers,
                                )
                                .error(),
                                &Real::two_to(-(s.target as i64)),
                            ) != Ordering::Greater)
                },
                LARGEST_M_LIMIT,
            )
        };
        m_once = sized(Scope::Once, 1, true);
        m_later = core::cmp::min(m_once, sized(Scope::Shared, requests, false));
    }
    if m_later == 0 {
        return false;
    }
    t.distances.m_once = m_once;
    t.distances.m_later = m_later;
    true
}

// ---------------------------------------------------------------------------------------------------------------------
// Which functions may add a round

/// `MayLay::close` (blocks.h:399-403): the setting's `instances` factor in the request scope, the
/// label `where`, and the nonce's label. `r` is what the round draws and states; the rest is set
/// by `Plan::close`, which returns `work_bits`.
fn may_close(
    p: &mut Plan,
    name: &str,
    where_: &str,
    kind: RoundKind,
    why: ErrorKind,
    mut error: Bound,
    priced: Priced,
    mut r: PlanRound,
) -> u32 {
    if p.scope() == Scope::Request && p.set.instances > 1 {
        error = error * Bound::from_big(&Big::from_u64(p.set.instances));
    }
    r.where_ = String::from(where_);
    let work_bits = p.close(name, kind, why, &error, priced, r);
    if work_bits != 0 && p.set.nonce_bytes != 0 {
        p.last_message_at(where_);
    }
    work_bits
}

/// `MayLay::enter` (blocks.h:404).
fn may_enter(p: &mut Plan, r: PlanRound) {
    p.enter(r);
}

/// `MayLay::none` (blocks.h:405).
fn may_none(p: &mut Plan, name: &str, where_: &str) {
    p.close_none(name, where_);
}

/// `MayLay::scalars` (blocks.h:406-409).
fn may_scalars(p: &mut Plan, what: &str, where_: &str, n: u64) {
    p.send_scalars(what, n);
    if n != 0 {
        p.last_message_at(where_);
    }
}

/// `MayLay::answers` (blocks.h:410-413).
fn may_answers(p: &mut Plan, where_: &str, n: u64) {
    p.send_answers("sample answers", n);
    if n != 0 {
        p.last_message_at(where_);
    }
}

/// `MayLay::roots` (blocks.h:414-416).
fn may_roots(p: &mut Plan, where_: &str, roots: u32) {
    for _ in 0..roots {
        p.send_root("root");
        p.last_message_at(where_);
    }
}

/// `MayLay::file` (blocks.h:417-420).
fn may_file(
    p: &mut Plan,
    what: &str,
    where_: &str,
    kind: MessageKind,
    bytes: u64,
    expected: f64,
    hash_calls: u64,
) {
    p.file(what, kind, bytes, expected, hash_calls);
    if bytes != 0 {
        p.last_message_at(where_);
    }
}

/// `MayLay::chain` (blocks.h:421).
fn may_chain(p: &mut Plan, o: &crate::numbers::plan::Planned) {
    p.append(o);
}

/// `MayLay::first_opening` (blocks.h:422): of a tree that may be opened at one list only.
fn first_opening(p: &mut Plan, tree: u64) -> bool {
    p.one_list_opened_mut().insert(tree)
}

// ---------------------------------------------------------------------------------------------------------------------
// Openings and small helpers

/// The answers to one list of `t` positions in one tree (`plan_open`, blocks.h:426-444).
pub fn plan_open(p: &mut Plan, where_: &str, callers_tr: &TreeSize, t: u64) {
    let tr = callers_tr.clone(); // READ ONCE (plan.h)
    let s = p.set.clone();
    if tr.one_list.yes {
        if tr.from_another_chain {
            p.refuse(&format!(
                "{}: the tree {} holds the mask of one step and is read in another chain",
                where_, tr.name
            ));
        }
        if !first_opening(p, tr.one_list.number) {
            p.refuse(&format!(
                "{}: the tree {} holds the mask of one step and is opened at a second list",
                where_, tr.name
            ));
        }
    }
    let main = expected_distinct(tr.log_n, t);
    // A leaf is hashed as label, symbols, salt. The salt never crosses a hash block's boundary.
    let calls = |bytes: u64| -> u64 {
        let before = s.label_bytes as u64 + bytes;
        let block = s.hash_block_bytes as u64;
        if before % block + s.salt_bytes as u64 <= block {
            (before + s.salt_bytes as u64 + block - 1) / block
        } else {
            (before + block - 1) / block + (s.salt_bytes as u64 + block - 1) / block
        }
    };
    let at = format!("{}, {}", where_, tr.name);
    may_file(
        p,
        "opened symbols",
        &at,
        MessageKind::Columns,
        t.wrapping_mul(tr.leaf_bytes),
        main * tr.leaf_bytes as f64,
        t.wrapping_mul(calls(tr.leaf_bytes)),
    );
    may_file(
        p,
        "salts",
        &at,
        MessageKind::Salts,
        t.wrapping_mul(s.salt_bytes as u64),
        main * s.salt_bytes as f64,
        0,
    );
    may_file(
        p,
        "paths",
        &at,
        MessageKind::Paths,
        path_digests_most(tr.log_n, t).wrapping_mul(s.digest_bytes as u64),
        path_digests_expected(tr.log_n, t) * s.digest_bytes as f64,
        t.wrapping_mul(tr.log_n as u64),
    );
}

/// A round with an empty verifier's message (`plan_none`, blocks.h:452).
pub fn plan_none(p: &mut Plan, name: &str, where_: &str) {
    may_none(p, name, where_);
}

/// `n` elements of E, named `what` (`plan_scalars`, blocks.h:455).
pub fn plan_scalars(p: &mut Plan, what: &str, where_: &str, n: u64) {
    may_scalars(p, what, where_, n);
}

/// `roots` Merkle roots (`plan_roots`, blocks.h:456).
pub fn plan_roots(p: &mut Plan, where_: &str, roots: u32) {
    may_roots(p, where_, roots);
}

/// An item of a file that is in no chain's message (`plan_file_item`, blocks.h:459).
pub fn plan_file_item(
    p: &mut Plan,
    what: &str,
    where_: &str,
    kind: MessageKind,
    bytes: u64,
    expected: f64,
    hash_calls: u64,
) {
    may_file(p, what, where_, kind, bytes, expected, hash_calls);
}

/// Appends the rounds and messages of a finished chain's plan (`plan_chain`, blocks.h:464-467).
pub fn plan_chain(p: &mut Plan, chain: &crate::numbers::plan::Planned) {
    may_chain(p, chain);
}

/// What a hash chain's part of a proof begins with: its salt (`plan_chain_start`, blocks.h:482-485).
pub fn plan_chain_start(p: &mut Plan, where_: &str, salted: bool) {
    if !salted {
        return;
    }
    let bytes = p.set.digest_bytes as u64;
    may_file(p, "chain salt", where_, MessageKind::Salts, bytes, bytes as f64, 0);
}

// ---------------------------------------------------------------------------------------------------------------------
// SEND, BAT, SPLIT

/// What a sample's error takes from one oracle message (`SampleSize`, blocks.h:511-514).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SampleSize {
    /// The number of variables of the sample's point.
    pub cube_bits: u32,
    /// The groups in which the message's rows are tested.
    pub groups: TestedIn,
}

/// A round that draws `elements` elements of E (`draws`, blocks.h:515-519).
pub fn draws(elements: u64) -> PlanRound {
    PlanRound { draw_e: elements, ..PlanRound::default() }
}

/// The largest list size among the groups (`list_of`, blocks.h:520-524).
pub fn list_of(p: &mut Plan, where_: &str, groups: &TestedIn) -> Big {
    let mut list = Big::from_u64(1);
    for g in groups.groups() {
        let a = analysis_group_in_plan(p, where_, g);
        if Big::cmp(&list, &a.list) == Ordering::Less {
            list = a.list;
        }
    }
    list
}

/// SEND for all oracle messages of one prover message (`plan_send`, blocks.h:531-544).
pub fn plan_send(
    p: &mut Plan,
    where_: &str,
    callers_o: &[SampleSize],
    roots: u32,
    answer_round: bool,
) {
    let o = callers_o.to_vec(); // READ ONCE (plan.h)
    let s = p.set.clone();
    may_roots(p, where_, roots);
    let mut e = Bound::from_u64(0);
    let mut cube = 0u32;
    for x in &o {
        let list = list_of(p, where_, &x.groups);
        e = e + sample_error(&s, &list, x.cube_bits, s.samples);
        cube = core::cmp::max(cube, x.cube_bits);
    }
    {
        let mut r = PlanRound::default();
        r.draw_e = s.samples as u64 * (cube as u64 + 1);
        r.draw_nonzero = s.samples as u64;
        may_close(p, R_SEND_SEED, where_, RoundKind::Seed, ErrorKind::Sample, e, Priced::OnTheCallersWord, r);
    }
    may_answers(p, where_, s.samples as u64 * o.len() as u64);
    if answer_round {
        plan_none(p, R_SEND_ANSWER, where_);
    }
}

/// BAT on the groups, `rows` linear claims (`plan_bat`, blocks.h:546-551).
pub fn plan_bat(p: &mut Plan, where_: &str, callers_groups: &TestedIn, rows: u64) {
    let groups = callers_groups.clone(); // READ ONCE (plan.h)
    let e = Bound::from_big(&list_of(p, where_, &groups)) * powers_error(&p.set, rows);
    let mut r = PlanRound::default();
    r.draw_e = 1;
    r.rows = rows;
    may_close(p, R_BAT, where_, RoundKind::Algebraic, ErrorKind::Field, e, Priced::OnTheCallersWord, r);
}

/// BAT-sigma: `rows` linear claims into one (`plan_bat_sigma`, blocks.h:552-556).
pub fn plan_bat_sigma(p: &mut Plan, where_: &str, rows: u64) {
    let e = powers_error(&p.set, rows);
    let mut r = PlanRound::default();
    r.draw_e = 1;
    r.rows = rows;
    may_close(p, R_BAT_SIGMA, where_, RoundKind::Algebraic, ErrorKind::Field, e, Priced::AsSaid, r);
}

/// SPLIT (`plan_split`, blocks.h:557-560).
pub fn plan_split(p: &mut Plan, where_: &str) {
    plan_scalars(p, "split target", where_, 1);
    plan_none(p, R_SPLIT, where_);
}

// ---------------------------------------------------------------------------------------------------------------------
// PSC, ZERO, LINE, product trees, RNG

/// The round polynomials' degrees (`PscSize`, blocks.h:570-575).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PscSize {
    /// The round polynomial of variable `j` has degree below `degree[j]`, at least 1.
    pub degree: Vec<u32>,
    /// The total degree of the summand in the maps that it evaluates.
    pub degree_y: u32,
    /// The values at the last point that the prover sends after Y's round.
    pub values: u32,
    /// False: the summand is affine; no further variable and no values are sent.
    pub with_y: bool,
}

impl Default for PscSize {
    fn default() -> Self {
        PscSize { degree: Vec::new(), degree_y: 2, values: 2, with_y: true }
    }
}

/// PSC: masked sumcheck for a polynomial summand (`plan_psc`, blocks.h:576-606).
pub fn plan_psc(p: &mut Plan, where_: &str, callers_x: &PscSize) {
    let x = callers_x.clone(); // READ ONCE (plan.h)
    let s = p.set.clone();
    let saved: u64 = if s.saved_coefficient { 1 } else { 0 };
    may_scalars(p, "hiding sum", where_, 1);
    may_close(
        p,
        R_PSC_EPSILON,
        where_,
        RoundKind::Epsilon,
        ErrorKind::Field,
        field_error(&s, 1),
        Priced::SettingAlone,
        draws(1),
    );
    let mut j = 0usize;
    while j < x.degree.len() {
        // p.compact: a run of equal rounds is entered once
        let mut run = 1usize;
        if p.compact {
            while j + run < x.degree.len() && x.degree[j + run] == x.degree[j] {
                run += 1;
            }
        }
        if run > 1 {
            p.push_repeat(run as u64);
        }
        let d = x.degree[j] as u64;
        may_scalars(p, "round polynomial", where_, d.wrapping_sub(saved));
        may_close(
            p,
            R_PSC_ROUND,
            where_,
            RoundKind::Algebraic,
            ErrorKind::Field,
            field_error(&s, d.wrapping_sub(1)),
            Priced::TheRoundItself,
            draws(1),
        );
        if run > 1 {
            p.pop_repeat();
        }
        j += run;
    }
    if !x.with_y {
        return;
    }
    may_scalars(p, "round polynomial in Y", where_, (x.degree_y as u64 + 1).wrapping_sub(saved));
    {
        let mut r = PlanRound::default();
        r.draw_e = 1;
        r.draw_nonzero = 1;
        may_close(
            p,
            R_PSC_Y,
            where_,
            RoundKind::Algebraic,
            ErrorKind::Field,
            field_error_nonzero(&s, x.degree_y as u64),
            Priced::TheRoundItself,
            r,
        );
    }
    may_scalars(p, "values at the last point", where_, x.values as u64);
    plan_none(p, R_PSC_VALUES, where_);
}

/// ZERO over `variables` variables (`plan_zero`, blocks.h:607-609).
pub fn plan_zero(p: &mut Plan, where_: &str, variables: u32) {
    let e = field_error(&p.set, variables as u64);
    may_close(
        p,
        R_ZERO,
        where_,
        RoundKind::Algebraic,
        ErrorKind::Field,
        e,
        Priced::TheRoundItself,
        draws(variables as u64),
    );
}

/// LINE (`plan_line`, blocks.h:610-612).
pub fn plan_line(p: &mut Plan, where_: &str) {
    let e = field_error(&p.set, 1);
    may_close(p, R_LINE, where_, RoundKind::Algebraic, ErrorKind::Field, e, Priced::SettingAlone, draws(1));
}

/// LKP shift: joins several lookup tables (`plan_shift`, blocks.h:616-618).
pub fn plan_shift(p: &mut Plan, where_: &str, union_entries: u64) {
    let e = field_error(&p.set, union_entries);
    may_close(
        p,
        R_LKP_SHIFT,
        where_,
        RoundKind::Algebraic,
        ErrorKind::Field,
        e,
        Priced::OnTheCallersWord,
        draws(1),
    );
}

/// JOIN: `2^variables` claims into one (`plan_join`, blocks.h:621-623).
pub fn plan_join(p: &mut Plan, where_: &str, variables: u32) {
    let e = field_error(&p.set, variables as u64);
    may_close(
        p,
        R_JOIN,
        where_,
        RoundKind::Algebraic,
        ErrorKind::Field,
        e,
        Priced::TheRoundItself,
        draws(variables as u64),
    );
}

/// LKP: the challenge at which two products over `2^keys_log` keys are compared (`plan_lkp`,
/// blocks.h:625-627).
pub fn plan_lkp(p: &mut Plan, where_: &str, keys_log: u32) {
    let num = Big::sub(&Big::two_to(keys_log as usize), &Big::from_u64(1));
    let e = Bound::ratio(&num, &p.set.card_e());
    may_close(p, R_LKP, where_, RoundKind::Algebraic, ErrorKind::Field, e, Priced::OnTheCallersWord, draws(1));
}

/// The levels of a product tree from the root down (`plan_product_tree`, blocks.h:632-639).
pub fn plan_product_tree(p: &mut Plan, where_: &str, levels: u32, more: u32) {
    for l in 0..levels {
        let mut x = PscSize::default();
        x.degree = vec![3; (l + more) as usize];
        plan_psc(p, where_, &x);
        plan_line(p, where_);
    }
}

/// BATT: batches `rows` claims on a table's matrix (`plan_batt`, blocks.h:643-648).
pub fn plan_batt(p: &mut Plan, where_: &str, rows: u64, k_col: u32) {
    plan_bat_sigma(p, where_, rows);
    let mut x = PscSize::default();
    x.degree = vec![3; k_col as usize];
    x.with_y = false;
    plan_psc(p, where_, &x);
}

/// One lookup's public sizes (`LookupSize`, blocks.h:657-665).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupSize {
    pub v: u32,
    pub d: u32,
    pub mu: u32,
    pub shifted: bool,
    /// How many of the `2^mu` bit positions are in use; 0: all.
    pub live: u32,
    /// log2 of each part's number of keys; empty: one part of `2^v` keys.
    pub parts: Vec<u32>,
}

impl Default for LookupSize {
    fn default() -> Self {
        LookupSize { v: 0, d: 0, mu: 0, shifted: false, live: 0, parts: Vec::new() }
    }
}

/// One lookup (LKP) (`plan_lookup`, blocks.h:666-700).
pub fn plan_lookup(p: &mut Plan, where_: &str, callers_x: &LookupSize) {
    let x = callers_x.clone(); // READ ONCE (plan.h)
    let slots: u64 = 1u64 << core::cmp::min(x.mu, 6);
    let w: u64 = if x.live != 0 { x.live as u64 } else { slots };
    let parts: Vec<u32> = if x.parts.is_empty() { vec![x.v] } else { x.parts.clone() };
    let mut keys = Big::zero();
    for v in &parts {
        keys = keys + Big::two_to(*v as usize);
    }
    if x.mu < 1 || x.mu > 6 || w < 2 || w > slots {
        p.refuse(&format!("{}: the look-up's sizes are not admitted", where_));
        return;
    }
    let two_w = Big::two_to(w as usize);
    let keys_fit = Big::cmp(&keys, &two_w) == Ordering::Less;
    let no_wrap = Big::cmp(
        &Big::mul(&Big::two_to(x.d as usize), &Big::sub(&two_w, &Big::from_u64(1))),
        &p.set.p,
    ) == Ordering::Less;
    if !keys_fit || !no_wrap {
        p.refuse(&format!("{}: the look-up's sizes are not admitted", where_));
        return;
    }
    if x.shifted {
        plan_shift(p, where_, 1u64 << x.d);
    }
    let e = Bound::ratio(&Big::sub(&keys, &Big::from_u64(1)), &p.set.card_e());
    may_close(p, R_LKP, where_, RoundKind::Algebraic, ErrorKind::Field, e, Priced::OnTheCallersWord, draws(1));
    let mut j: u64 = 0;
    while j + 1 < w {
        let run: u64 = if j != 0 && p.compact { w - 1 - j } else { 1 }; // all steps but the first are alike
        let mut step = PscSize::default();
        step.degree_y = 3;
        step.values = if j != 0 { 2 } else { 3 };
        if run > 1 {
            p.push_repeat(run);
        }
        plan_psc(p, &format!("{}, tie", where_), &step);
        if run > 1 {
            p.pop_repeat();
        }
        j += run;
    }
    for _ in 0..parts.len().saturating_sub(1) {
        // from the product of the parts' roots to each root
        plan_psc(p, &format!("{}, parts", where_), &PscSize::default());
    }
    plan_join(p, where_, x.mu);
    for v in &parts {
        plan_product_tree(p, &format!("{}, keys", where_), *v, 0);
    }
    plan_product_tree(p, &format!("{}, table", where_), x.d, x.mu);
    let mut leaves = PscSize::default();
    leaves.degree = vec![3; x.d as usize];
    leaves.degree.extend(vec![2; x.mu as usize]);
    leaves.with_y = false;
    plan_psc(p, &format!("{}, leaves", where_), &leaves);
    plan_zero(p, &format!("{}, bits", where_), x.mu + x.d);
    let mut bits = PscSize::default();
    bits.degree = vec![3; (x.mu + x.d) as usize];
    bits.degree_y = 2;
    bits.values = 1;
    plan_psc(p, &format!("{}, bits", where_), &bits);
}

/// The number of combinations of RNG's matrix (`rng_combinations`, blocks.h:706-709).
pub fn rng_combinations(s: &Setting, scope: Scope) -> u32 {
    let w = s.work_of(ErrorKind::Small, scope);
    (if s.target > w { s.target - w } else { 0 })
        + if scope == Scope::Request { ceil_log2(s.instances) } else { 0 }
}

/// As `rng_combinations`, under the plan's setting and scope (`blocks.h:710`).
pub fn rng_combinations_plan(p: &Plan) -> u32 {
    rng_combinations(&p.set, p.scope())
}

/// RNG: the matrix of the approximate range check (`plan_rng`, blocks.h:712-718).
pub fn plan_rng(p: &mut Plan, where_: &str, columns: u64) {
    let n = rng_combinations_plan(p);
    if n != 0 && columns > (u64::MAX - 31) / n as u64 {
        p.refuse(&format!(
            "{}: so many columns that the number of drawn entries does not fit 64 bits",
            where_
        ));
        return;
    }
    let mut r = PlanRound::default();
    r.draw_trits = columns * n as u64;
    r.combinations = n as u64;
    let e = Bound::from_real(&Real::two_to(-(n as i64)));
    may_close(p, R_RNG, where_, RoundKind::Bits, ErrorKind::Small, e, Priced::AsSaid, r);
}

// ---------------------------------------------------------------------------------------------------------------------
// FOLD, LOC, CS and BASE; IOPP

/// FOLD (`plan_fold`, blocks.h:726-735).
pub fn plan_fold(p: &mut Plan, where_: &str, callers_g: &GroupSize, roots: u32) {
    let g = callers_g.clone(); // READ ONCE (plan.h)
    let a = analysis_group_in_plan(p, where_, &g);
    may_roots(p, where_, roots);
    may_scalars(p, "hiding sum", where_, 1);
    let e = Bound::from_big(&a.list) * field_error(&p.set, 1);
    let mut r = PlanRound::default();
    r.draw_e = 1;
    r.group = priced_group(&g);
    may_close(p, R_FOLD_EPSILON, where_, RoundKind::Epsilon, ErrorKind::Field, e, Priced::AsSaid, r);
    plan_fold_rounds(p, where_, &g);
}

/// FOLD's rounds `j = 1..k` (`plan_fold_rounds`, blocks.h:736-751).
pub fn plan_fold_rounds(p: &mut Plan, where_: &str, callers_g: &GroupSize) {
    let g = callers_g.clone(); // READ ONCE (plan.h)
    let s = p.set.clone();
    let a = analysis_group_in_plan(p, where_, &g);
    let mut j = 1u32;
    while j <= g.k {
        let mut run = 1u32; // past the mask's h variables all errors are equal
        if p.compact && (!g.has_mask() || j > g.h) {
            run = g.k - j + 1;
        }
        if run > 1 {
            p.push_repeat(run as u64);
        }
        may_scalars(p, "round polynomial", where_, if s.saved_coefficient { 2 } else { 3 });
        let mut r = PlanRound::default();
        r.draw_e = 1;
        r.rests = if g.has_mask() && j <= g.h { weakest_source(&a) } else { a.at.source };
        r.group = priced_group(&g);
        let e = fold_round_error(&s, &g, &a, j);
        may_close(p, R_FOLD_ROUND, where_, RoundKind::Algebraic, ErrorKind::Closeness, e, Priced::AsSaid, r);
        if run > 1 {
            p.pop_repeat();
        }
        j += run;
    }
}

/// LOC: `t` positions of a group (`plan_loc`, blocks.h:754-765). Returns `t`.
pub fn plan_loc(
    p: &mut Plan,
    where_: &str,
    callers_g: &GroupSize,
    callers_trees: &[TreeSize],
) -> u64 {
    let g = callers_g.clone(); // READ ONCE (plan.h)
    let trees = callers_trees.to_vec();
    let a = analysis_group_in_plan(p, where_, &g);
    let t = plan_positions_default(p, &a.at.agree);
    if t == 0 {
        p.refuse(&format!("{}: no number of positions reaches the target", where_));
    }
    let mut r = PlanRound::default();
    r.draw_positions = t;
    r.log_n = g.main.log_n;
    r.group = priced_codes(&g);
    let e = Bound::pow(&a.at.agree, t);
    may_close(p, R_LOC, where_, RoundKind::Positions, ErrorKind::Query, e, Priced::AsSaid, r);
    for tr in &trees {
        plan_open(p, where_, tr, t);
    }
    t
}

/// CS: the new oracle message, its sample, and the positions (`plan_cs`, blocks.h:772-798).
/// Returns the number of positions.
pub fn plan_cs(
    p: &mut Plan,
    where_: &str,
    callers_from: &GroupSize,
    callers_to: &GroupSize,
    cube_bits: u32,
    old_rows: u64,
    symbols: u32,
    callers_trees: &[TreeSize],
    roots: u32,
) -> u64 {
    let from = callers_from.clone(); // READ ONCE (plan.h)
    let to = callers_to.clone();
    let trees = callers_trees.to_vec();
    let a = analysis_group_in_plan(p, where_, &from);
    let next_stage = analysis_group_in_plan(p, &format!("{}: the stage that follows", where_), &to);
    plan_send(
        p,
        where_,
        &[SampleSize { cube_bits, groups: TestedIn::new(&to) }],
        roots,
        false,
    );
    // The round's error is agree^t plus a batching term that grows with t. So t is iterated from 0:
    // each step takes the smallest t that suffices with the batching term of the step before.
    let mut t: u64 = 0;
    loop {
        let rows = old_rows + p.set.samples as u64 + symbols as u64 * t;
        let extra = Bound::from_big(&next_stage.list) * powers_error(&p.set, rows);
        let next = plan_positions(p, &a.at.agree, &extra);
        if next == t || next == 0 {
            t = next;
            break;
        }
        t = next;
    }
    if t == 0 {
        p.refuse(&format!("{}: no number of positions reaches the target", where_));
    }
    let rows = old_rows + p.set.samples as u64 + symbols as u64 * t;
    let mut r = PlanRound::default();
    r.draw_positions = t;
    r.log_n = from.main.log_n;
    r.draw_e = 1;
    r.rows = rows;
    r.group = priced_codes(&from);
    let e = Bound::pow(&a.at.agree, t)
        + Bound::from_big(&next_stage.list) * powers_error(&p.set, rows);
    may_close(p, R_CS, where_, RoundKind::Positions, ErrorKind::Query, e, Priced::OnTheCallersWord, r);
    for tr in &trees {
        plan_open(p, where_, tr, t);
    }
    t
}

/// BASE (`plan_base`, blocks.h:801-821). Returns the number of positions.
pub fn plan_base(
    p: &mut Plan,
    where_: &str,
    callers_g: &GroupSize,
    callers_trees: &[TreeSize],
    roots: u32,
) -> u64 {
    let g = callers_g.clone(); // READ ONCE (plan.h)
    let trees = callers_trees.to_vec();
    let s = p.set.clone();
    let a = analysis_group_in_plan(p, where_, &g);
    may_roots(p, where_, roots);
    may_scalars(p, "masked target", where_, 1);
    {
        let mut r = PlanRound::default();
        r.draw_e = 1;
        r.rests = weakest_source(&a);
        r.group = priced_group(&g);
        let e = base_error(&s, &g, &a);
        may_close(p, R_BASE_LAMBDA, where_, RoundKind::Algebraic, ErrorKind::Closeness, e, Priced::AsSaid, r);
    }
    let n = g.main.coordinates() * g.slots + if g.has_mask() { g.mask.coordinates() } else { 0 };
    may_scalars(p, "masked message and randomness", where_, n);
    let t = plan_positions_default(p, &a.at.agree);
    if t == 0 {
        p.refuse(&format!("{}: no number of positions reaches the target", where_));
    }
    let mut r = PlanRound::default();
    r.draw_positions = t;
    r.log_n = g.main.log_n;
    r.group = priced_codes(&g);
    let e = Bound::pow(&a.at.agree, t);
    may_close(p, R_BASE, where_, RoundKind::Positions, ErrorKind::Query, e, Priced::AsSaid, r);
    for tr in &trees {
        plan_open(p, where_, tr, t);
    }
    t
}

/// A list longer than the stage's random coordinates were sized for (`plan_iopp`, blocks.h:927-929).
fn within(p: &mut Plan, where_: &str, t: u64, x: &Stage) {
    if t > x.t {
        p.refuse(&format!(
            "{}: a list is longer than the stage's random coordinates were sized for",
            where_
        ));
    }
}

/// IOPP: a whole proximity test (`plan_iopp`, blocks.h:920-956). `last` numbers marked trees
/// (`OneList`), as `OneList::mark` expects; the C++ header keeps that counter in a static.
pub fn plan_iopp(
    p: &mut Plan,
    where_: &str,
    st: &[Stage],
    first_trees: &[TreeSize],
    rows: u64,
    first_mask_roots: u32,
    masks_ride: bool,
    last: &mut u64,
) {
    let s = p.set.clone();
    if st.len() < 2 {
        p.refuse(&format!("{}: a proximity test has at least two stages", where_));
        return;
    }
    plan_bat(p, where_, &TestedIn::new(&st[0].g), rows);
    let mut trees: Vec<TreeSize> = first_trees.to_vec();
    for i in 0..st.len() - 1 {
        let g = st[i].g.clone();
        let n = st[i + 1].g.clone();
        let w = format!("{}, stage {}", where_, i + 1);
        plan_fold(p, &w, &g, if i != 0 { if masks_ride { 0 } else { 1 } } else { first_mask_roots });
        if g.has_mask() && (if i != 0 { !masks_ride } else { first_mask_roots != 0 }) {
            let mut m = TreeSize::default();
            m.name = String::from("fresh mask");
            m.log_n = g.mask.log_n;
            m.leaf_bytes = (s.e_bytes as u64) << g.h;
            m.one_list.mark(true, last);
            trees.push(m);
        }
        let symbols = g.slots as u32 + if g.has_mask() { 2 } else { 0 };
        let t = plan_cs(p, &w, &g, &n, stage_cube_bits(&n), 1, symbols, &trees, 1);
        within(p, where_, t, &st[i]);
        let mut sw = TreeSize::default();
        sw.name = String::from("switch oracle");
        sw.log_n = n.main.log_n;
        // the stage's rows; copies of its mask rows and, with `masks_ride`, of its fold's fresh mask
        sw.leaf_bytes = ((s.e_bytes as u64) << n.k)
            + ((s.e_bytes as u64) << n.h) * if masks_ride { 2 } else { 1 };
        if masks_ride && i + 2 == st.len() {
            sw.leaf_bytes += s.e_bytes as u64;
        }
        sw.one_list.mark(masks_ride, last);
        trees = vec![sw];
    }
    let b = st.last().unwrap().g.clone();
    if !masks_ride {
        let mut m = TreeSize::default();
        m.name = String::from("masking codeword");
        m.log_n = b.main.log_n;
        m.leaf_bytes = 2 * (s.e_bytes as u64);
        m.one_list.mark(true, last);
        trees.push(m);
    }
    let t = plan_base(p, &format!("{}, last stage", where_), &b, &trees, if masks_ride { 0 } else { 1 });
    within(p, where_, t, st.last().unwrap());
}

// ---------------------------------------------------------------------------------------------------------------------
// The committed table: RECORD, LIN, LINK

/// RECORD: the table's record (`plan_record`, blocks.h:1060-1072).
pub fn plan_record(p: &mut Plan, where_: &str, callers_t: &TableSize) {
    let t = callers_t.clone(); // READ ONCE (plan.h)
    let a = analysis_table_in_plan(p, where_, &t);
    if t.answers == 0 {
        return; // the plan was rejected above; there is no message to plan
    }
    let cube = ceil_log2(t.code.ell);
    let e = sample_error(&p.set, &a.once.list, cube, t.answers);
    let mut r = PlanRound::default();
    r.name = String::from(R_RECORD);
    r.where_ = String::from(where_);
    r.kind = RoundKind::Record;
    r.why = ErrorKind::Sample;
    r.scope = p.scope();
    r.count = p.times();
    r.error = e.error();
    r.priced = Priced::OnTheCallersWord; // no channel closes this round
    r.draw_e = t.answers as u64 * (cube as u64 + 1);
    r.draw_nonzero = t.answers as u64;
    may_enter(p, r);
    let answers = ((t.answers as u64) << t.v) * p.set.e_bytes as u64;
    may_file(p, "record", where_, MessageKind::Answers, answers, answers as f64, 0);
}

/// The query that ends a chain (`plan_seal`, blocks.h:1099-1101).
pub fn plan_seal(p: &mut Plan, where_: &str) {
    may_close(
        p,
        R_SEAL,
        where_,
        RoundKind::Seal,
        ErrorKind::Zero,
        Bound::from_u64(0),
        Priced::Nothing,
        PlanRound::default(),
    );
}

/// A sample and the further oracle messages in its prover message (`with_riders`, blocks.h:1102-1106).
pub fn with_riders(first: &SampleSize, beside: &[SampleSize]) -> Vec<SampleSize> {
    let mut v = vec![first.clone()];
    v.extend_from_slice(beside);
    v
}

/// LIN's first part: W and its sample (`plan_lin_first`, blocks.h:1107-1109).
pub fn plan_lin_first(p: &mut Plan, where_: &str, x: &LinSize) {
    plan_send(p, &format!("{}, W", where_), &with_riders(&x.w, &x.beside_w), x.roots_w, true);
}

/// LIN's shared part (`plan_lin_shared`, blocks.h:1110-1134). Returns the number of columns.
pub fn plan_lin_shared(
    p: &mut Plan,
    where_: &str,
    callers_t: &TableSize,
    callers_x: &LinSize,
    callers_tree: &TreeSize,
) -> u64 {
    let t = callers_t.clone(); // READ ONCE (plan.h)
    let x = callers_x.clone();
    let tree = callers_tree.clone();
    let s = p.set.clone();
    let a = analysis_table_in_plan(p, where_, &t);
    let at = if x.one_time { a.once.clone() } else { a.later.clone() };
    let test = if x.one_time { TableTest::OneTime } else { TableTest::Later };
    let point = Bound::from_big(&Big::from_u64(x.instances))
        * field_error(&s, t.v as u64 + x.k_lo as u64)
        + table_fold_error(&s, &t, &at);
    {
        let mut r = PlanRound::default();
        r.draw_e = t.v as u64 + x.k_lo as u64;
        r.rests = at.source;
        r.table = priced_table(&t, test);
        r.sharing = x.instances;
        may_close(p, R_LIN_POINT, where_, RoundKind::Algebraic, ErrorKind::Closeness, point, Priced::OnTheCallersWord, r);
    }
    plan_send(p, &format!("{}, folded row", where_), &[x.u.clone()], x.roots_u, true);
    let agree = at.agree.clone();
    let nu = plan_positions_default(p, &agree);
    if nu == 0 {
        p.refuse(&format!("{}: no number of columns reaches the target", where_));
    }
    let mut r = PlanRound::default();
    r.draw_positions = nu;
    r.log_n = t.code.log_n;
    r.table = priced_table(&t, test);
    let e = Bound::pow(&agree, nu);
    may_close(
        p,
        R_LOC,
        &format!("{}, columns", where_),
        RoundKind::Positions,
        ErrorKind::Query,
        e,
        Priced::OnTheCallersWord,
        r,
    );
    plan_open(p, where_, &tree, nu);
    plan_send(p, &format!("{}, Omega", where_), &with_riders(&x.omega, &x.beside_omega), x.roots_omega, true);
    let e = field_error(&s, x.rows_log as u64);
    may_close(p, R_LIN_ZETA, where_, RoundKind::Algebraic, ErrorKind::Field, e, Priced::TheRoundItself, draws(x.rows_log as u64));
    nu
}

/// LINK: ties a further committed table to the anchor (`plan_link`, blocks.h:1141-1173). Returns
/// `(nu_first, nu_further)`, the two lists of columns.
pub fn plan_link(
    p: &mut Plan,
    where_: &str,
    callers_t: &TableSize,
    callers_u: &SampleSize,
    callers_tree: &TreeSize,
) -> (u64, u64) {
    let t = callers_t.clone(); // READ ONCE (plan.h)
    let u = callers_u.clone();
    let tree = callers_tree.clone();
    let s = p.set.clone();
    let a = analysis_table_in_plan(p, where_, &t);
    let first = a.later.clone();
    let e = field_error(&s, t.v as u64)
        + table_fold_error(&s, &t, &a.once)
        + table_fold_error(&s, &t, &first);
    {
        let mut r = PlanRound::default();
        r.draw_e = t.v as u64;
        r.rests = if source_rank(first.source) > source_rank(a.once.source) { first.source } else { a.once.source };
        r.table = priced_table(&t, TableTest::Link);
        may_close(p, R_LINK_POINT, where_, RoundKind::Algebraic, ErrorKind::Closeness, e, Priced::OnTheCallersWord, r);
    }
    may_roots(p, where_, 1);
    {
        let list = list_of(p, where_, &u.groups);
        let e = Bound::from_u64(2) * sample_error(&s, &list, u.cube_bits, s.samples);
        let mut r = PlanRound::default();
        r.draw_e = s.samples as u64 * (u.cube_bits as u64 + 1);
        r.draw_nonzero = s.samples as u64;
        may_close(p, R_SEND_SEED, where_, RoundKind::Seed, ErrorKind::Sample, e, Priced::OnTheCallersWord, r);
    }
    may_answers(p, where_, 2 * s.samples as u64);
    plan_none(p, R_SEND_ANSWER, where_);
    let a0 = first.agree.clone();
    let aj = a.once.agree.clone();
    let nu_first = plan_positions_default(p, &a0);
    let nu_further = plan_positions_default(p, &aj); // the caller's two numbers are never read
    if nu_first == 0 || nu_further == 0 {
        p.refuse(&format!("{}: no number of columns reaches the target", where_));
    }
    let e0 = Bound::pow(&a0, nu_first);
    let ej = Bound::pow(&aj, nu_further);
    let mut r = PlanRound::default();
    r.draw_positions = nu_first + nu_further;
    r.log_n = t.code.log_n;
    r.first_list = nu_first;
    r.table = priced_table(&t, TableTest::Link);
    let e = if Real::cmp(&e0.hi, &ej.hi) == Ordering::Less { ej } else { e0 };
    may_close(p, R_LINK, where_, RoundKind::Positions, ErrorKind::Query, e, Priced::OnTheCallersWord, r);
    plan_open(p, &format!("{}, first table", where_), &tree, nu_first);
    plan_open(p, &format!("{}, further table", where_), &tree, nu_further);
    let e = field_error(&s, ceil_log2(t.code.ell) as u64);
    may_close(
        p,
        R_LINK_PHI,
        where_,
        RoundKind::Algebraic,
        ErrorKind::Field,
        e,
        Priced::TheRoundItself,
        draws(ceil_log2(t.code.ell) as u64),
    );
    (nu_first, nu_further)
}

/// LIN's public sizes (`LinSize`, blocks.h:1090-1097).
#[derive(Clone, Debug)]
pub struct LinSize {
    /// The sample sizes of W, the re-encoded folded row and Omega.
    pub w: SampleSize,
    pub u: SampleSize,
    pub omega: SampleSize,
    /// How many requests share the point.
    pub instances: u64,
    /// The low variables of the shared point.
    pub k_lo: u32,
    /// The variables of the point of comparison.
    pub rows_log: u32,
    /// Further oracle messages in W's and in Omega's prover message.
    pub beside_w: Vec<SampleSize>,
    pub beside_omega: Vec<SampleSize>,
    /// The committer's own test, at delta_M.
    pub one_time: bool,
    pub roots_w: u32,
    pub roots_u: u32,
    pub roots_omega: u32,
}

impl LinSize {
    /// A `LinSize` with the C++ defaults (blocks.h:1090-1097).
    pub fn new(w: SampleSize, u: SampleSize, omega: SampleSize) -> Self {
        LinSize {
            w,
            u,
            omega,
            instances: 1,
            k_lo: 0,
            rows_log: 0,
            beside_w: Vec::new(),
            beside_omega: Vec::new(),
            one_time: false,
            roots_w: 1,
            roots_u: 1,
            roots_omega: 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn goldilocks(target: u32) -> Setting {
        let mut s = Setting::goldilocks();
        s.target = target;
        s
    }

    fn group_small() -> GroupSize {
        GroupSize {
            name: String::from("small"),
            main: CodeSize {
                name: String::from("small"),
                log_n: 4,
                ell: 4,
                r: 4,
                over_e: false,
            },
            ..GroupSize::default()
        }
    }

    fn real_eq(a: &Real, b: &Real) -> bool {
        Real::cmp(a, b) == Ordering::Equal
    }

    #[test]
    fn default_group_load_matches_the_header() {
        let l = GroupLoad::default();
        assert_eq!(l.cube_bits, 40);
        assert_eq!(l.messages, 4);
        assert_eq!(l.batched_rows, 1 << 20);
    }

    #[test]
    fn priced_copies_the_public_numbers() {
        let mut g = group_small();
        g.k = 2;
        g.h = 1;
        g.slots = 3;
        g.m = 7;
        g.mask = CodeSize { name: String::from("m"), log_n: 3, ell: 4, r: 2, over_e: true };
        let p = priced_group(&g);
        assert!(p.said);
        assert_eq!(p.main, PricedCode { log_n: 4, ell: 4, r: 4 });
        assert_eq!(p.mask, PricedCode { log_n: 3, ell: 4, r: 2 });
        assert_eq!((p.k, p.h, p.slots), (2, 1, 3));
        assert_eq!((p.rule, p.m), (Radius::Johnson as u32, 7));

        let no_mask = priced_group(&group_small());
        assert_eq!(no_mask.mask, PricedCode::default());

        let codes = priced_codes(&g);
        assert_eq!((codes.k, codes.h, codes.slots), (0, 0, 1));
        assert_eq!(codes.main, p.main);
        assert_eq!(codes.mask, p.mask);
    }

    #[test]
    fn mask_rules_compares_the_two_rates() {
        let s = Setting::goldilocks();
        let main = CodeSize { name: String::new(), log_n: 4, ell: 8, r: 4, over_e: false };
        let mut mask = CodeSize { name: String::new(), log_n: 3, ell: 4, r: 4, over_e: false };
        // main: k = 11 over n = 16; mask: k = 7 over n = 8. 7/8 > 11/16.
        assert!(mask_rules(&s, &GroupSize { main: main.clone(), mask: mask.clone(), ..GroupSize::default() }));
        mask.ell = 1;
        mask.r = 1;
        // mask: k = 1 over n = 8 < 11/16.
        assert!(!mask_rules(&s, &GroupSize { main: main.clone(), mask, ..GroupSize::default() }));
        assert!(!mask_rules(&s, &group_small()));
    }

    #[test]
    fn shape_fault_names_each_rejected_shape() {
        let s = Setting::goldilocks();
        let no_mask = group_small();
        assert_eq!(shape_fault(&s, &no_mask), None);
        let mut h_without_mask = group_small();
        h_without_mask.h = 1;
        assert_eq!(shape_fault(&s, &h_without_mask), Some("mask rows without a mask code"));

        let mut longer_mask = group_small();
        longer_mask.mask = CodeSize { name: String::new(), log_n: 5, ell: 1, r: 1, over_e: false };
        assert_eq!(shape_fault(&s, &longer_mask), Some("the mask code is longer than the main code"));

        let mut h_too_big = group_small();
        h_too_big.k = 1;
        h_too_big.h = 2;
        h_too_big.mask = CodeSize { name: String::new(), log_n: 3, ell: 1, r: 1, over_e: false };
        assert_eq!(
            shape_fault(&s, &h_too_big),
            Some("more row variables for the mask rows than for the main rows")
        );

        // k > 0, h = 0 and a mask code of a larger rate.
        let mut single_mask = group_small();
        single_mask.k = 3;
        single_mask.mask = CodeSize { name: String::new(), log_n: 3, ell: 4, r: 4, over_e: false };
        assert_eq!(
            shape_fault(&s, &single_mask),
            Some("a single mask row beside rows that are folded has a code of a larger rate than theirs: lengthen the mask code")
        );
    }

    #[test]
    fn analysis_at_shares_the_list_and_reads_the_mask_code() {
        let s = Setting::goldilocks();
        let at = Proximity {
            agree: Bound::ratio(&Big::from_u64(19), &Big::from_u64(20)),
            delta: Bound::ratio(&Big::from_u64(1), &Big::from_u64(20)),
            eta: Bound::default(),
            m: 3,
            from_m: true,
            source: CountSource::Third,
            count: Bound::from_u64(5),
            list: Big::from_u64(2),
        };
        let g = GroupSize {
            k: 3,
            h: 1,
            mask: CodeSize { name: String::new(), log_n: 2, ell: 2, r: 2, over_e: false },
            ..group_small()
        };
        let a = analysis_at(&s, &g, &at);
        assert!(a.with_mask);
        assert_eq!(a.fault, None);
        assert!(!a.bad());
        assert_eq!(a.list, Big::from_u64(2));
        // The mask code is read at the main code's length: k = 3 << 2 = 12, n = 16.
        // delta = 1 / 20 gives floor(16/20) = 0 errors, so 3 * 0 < 16 - 12: the THIRD branch.
        assert_eq!(a.mask_at.source, CountSource::Third);
        assert!(real_eq(&a.mask_at.count.hi, &Real::from_u64(1)));
        assert_eq!(a.mask_at.list, Big::from_u64(1));
        assert!(real_eq(&a.mask_at.agree.hi, &at.agree.hi));

        let mut faulty = g.clone();
        faulty.h = 0;
        faulty.k = 3;
        let b = analysis_at(&s, &faulty, &at);
        assert!(b.bad());
        assert_eq!(b.fault, Some("a single mask row beside rows that are folded has a code of a larger rate than theirs: lengthen the mask code"));
    }

    #[test]
    fn fold_and_base_errors_add_their_terms() {
        // card_E = p^degree = 2, so mca = count / 2 and field_error(d) = d / 2.
        let s = Setting { p: Big::from_u64(2), degree: 1, ..Setting::default() };
        let at = Proximity {
            agree: Bound::from_u64(1),
            delta: Bound::from_u64(0),
            eta: Bound::default(),
            m: 3,
            from_m: true,
            source: CountSource::Third,
            count: Bound::from_u64(1),
            list: Big::from_u64(1),
        };
        let a = Analysis {
            at: at.clone(),
            list: Big::from_u64(1),
            ..Analysis::default()
        };
        let g = group_small();
        // mca = 1/2; + list * field_error(1) = 1/2.
        let base = base_error(&s, &g, &a);
        assert!(!base.bad);
        assert!(real_eq(&base.error(), &Real::from_u64(1)));
        // mca = 1/2; + list * field_error(2) = 1.
        let fold = fold_round_error(&s, &g, &a, 1);
        assert!(real_eq(&fold.error(), &Real::div(&Real::from_u64(3), &Real::from_u64(2), Dir::Down)));

        // With a mask row at the first row variable: fold adds 2 * mca(mask) = 1,
        // base adds mca(mask) = 1/2.
        let mut gm = g.clone();
        gm.mask = CodeSize { name: String::new(), log_n: 2, ell: 1, r: 0, over_e: false };
        gm.h = 1;
        let am = Analysis {
            at,
            mask_at: Proximity {
                agree: Bound::from_u64(1),
                delta: Bound::from_u64(0),
                eta: Bound::default(),
                m: 3,
                from_m: true,
                source: CountSource::Third,
                count: Bound::from_u64(1),
                list: Big::from_u64(1),
            },
            list: Big::from_u64(1),
            fault: None,
            with_mask: true,
        };
        assert!(real_eq(&fold_round_error(&s, &gm, &am, 1).error(), &Real::div(&Real::from_u64(5), &Real::from_u64(2), Dir::Down)));
        assert!(real_eq(&fold_round_error(&s, &gm, &am, 2).error(), &Real::div(&Real::from_u64(3), &Real::from_u64(2), Dir::Down)));
        assert!(real_eq(&base_error(&s, &gm, &am).error(), &Real::div(&Real::from_u64(3), &Real::from_u64(2), Dir::Down)));
    }

    #[test]
    fn goal_of_divides_by_instances_only_per_request() {
        let mut s = Setting::default();
        s.target = 10;
        s.set_work(ErrorKind::Closeness, Scope::Shared, 12);
        s.set_work(ErrorKind::Closeness, Scope::Request, 12);
        s.set_work(ErrorKind::Closeness, Scope::Once, 12);
        s.instances = 3;
        assert!(real_eq(&goal_of(&s, ErrorKind::Closeness, Scope::Shared), &Real::from_u64(4)));
        assert!(real_eq(&goal_of(&s, ErrorKind::Closeness, Scope::Once), &Real::from_u64(4)));
        let r = goal_of(&s, ErrorKind::Closeness, Scope::Request);
        // 4 / 3, rounded down.
        assert_eq!(Real::cmp(&r, &Real::from_u64(1)), Ordering::Greater);
        assert_eq!(Real::cmp(&r, &Real::from_u64(2)), Ordering::Less);
        s.instances = 1;
        assert!(real_eq(&goal_of(&s, ErrorKind::Closeness, Scope::Request), &Real::from_u64(4)));
    }

    #[test]
    fn group_holds_at_a_small_target_and_not_at_a_large_one() {
        let g = group_small();
        let load = GroupLoad::default();
        // With card_E about 2^192 and errors of order 2^5, the target 1 is met for every m up to
        // the cap; the target 200 is not met by any.
        let small = goldilocks(1);
        let m3 = group_of_m(&g, 3);
        assert!(group_holds(&small, Scope::Request, &m3, &load));
        let sized = size_group(&small, Scope::Request, &g, &load);
        // The closeness term grows like m^5, so the largest m is below the cap but still large:
        // at m = 2^30 the count is about 2^155 and its error about 2^-37, well below 1/2.
        assert!(sized.m > 1 << 30);
        assert!(sized.m < LARGEST_M_LIMIT);
        assert_eq!(sized.rule, Radius::Johnson);
        assert!(group_holds(&small, Scope::Request, &sized, &load));
        assert!(!analysis_group(&small, &sized).bad());

        let large = goldilocks(200);
        assert!(!group_holds(&large, Scope::Request, &m3, &load));
        let none = size_group(&large, Scope::Request, &g, &load);
        assert_eq!(none.m, 0);
        assert!(analysis_group(&large, &none).bad());
    }

    #[test]
    fn scope_positions_counts_the_extra_term_and_the_instances() {
        let mut s = Setting::default();
        s.target = 3;
        s.set_work(ErrorKind::Query, Scope::Request, 0);
        s.instances = 1;
        let half = Bound::ratio(&Big::from_u64(1), &Big::from_u64(2));
        let zero = Bound::from_u64(0);
        assert_eq!(scope_positions(&s, Scope::Request, &half, &zero), 3);
        // (1/2)^t <= 2^-3 / 2 = 2^-4.
        s.instances = 2;
        assert_eq!(scope_positions(&s, Scope::Request, &half, &zero), 4);
        // A request's instances do not divide a shared round.
        assert_eq!(scope_positions(&s, Scope::Shared, &half, &zero), 3);
        s.instances = 1;
        // extra = 1/16: (1/2)^t + 1/16 <= 1/8 at t = 4.
        assert_eq!(
            scope_positions(&s, Scope::Request, &half, &Bound::ratio(&Big::from_u64(1), &Big::from_u64(16))),
            4
        );
        assert_eq!(scope_positions_default(&s, Scope::Request, &half), 3);
    }

    #[test]
    fn positions_from_below_drops_the_mask_and_reports_no_distance() {
        let g = group_small();
        let load = GroupLoad::default();
        let small = goldilocks(1);
        assert!(positions_from_below(&small, Scope::Request, g.clone(), &load, &Bound::from_u64(0)) > 0);
        let large = goldilocks(200);
        assert_eq!(positions_from_below(&large, Scope::Request, g, &load, &Bound::from_u64(0)), 0);
    }

    #[test]
    fn weakest_source_takes_the_larger_rank() {
        let mut a = Analysis {
            with_mask: true,
            at: Proximity { source: CountSource::Johnson, ..Proximity::default() },
            mask_at: Proximity { source: CountSource::Third, ..Proximity::default() },
            ..Analysis::default()
        };
        assert_eq!(weakest_source(&a), CountSource::Johnson);
        a.mask_at.source = CountSource::Johnson;
        assert_eq!(weakest_source(&a), CountSource::Johnson);
        a.at.source = CountSource::Third;
        assert_eq!(weakest_source(&a), CountSource::Johnson);
        a.with_mask = false;
        assert_eq!(weakest_source(&a), CountSource::Third);
    }

    #[test]
    fn tree_size_helpers_match_the_closed_forms() {
        assert_eq!(expected_distinct(0, 1), 1.0);
        assert!((expected_distinct(1, 2) - 1.5).abs() < 1e-12);
        assert!((expected_distinct(10, 1) - 1.0).abs() < 1e-12);
        assert_eq!(path_digests_most(0, 5), 0);
        assert_eq!(path_digests_most(3, 0), 0);
        assert_eq!(path_digests_most(3, 1), 3);
        assert_eq!(path_digests_most(3, 2), 4);
        assert_eq!(path_digests_most(3, 3), 4);
        assert_eq!(path_digests_most(3, 5), 4);
        assert!((path_digests_expected(3, 1) - 3.0).abs() < 1e-12);
        assert_eq!(path_digests_expected(0, 3), 0.0);
        // Known values: numbers_test.cpp:265-273.
        assert_eq!(path_digests_most(23, 335), 4867);
        assert!(path_digests_expected(23, 335) <= path_digests_most(23, 335) as f64);
        assert!((expected_distinct(10, 60) - 1024.0 * (1.0 - libm::pow(1023.0 / 1024.0, 60.0))).abs() < 1e-6);
    }

    #[test]
    fn one_list_assigns_each_marked_tree_a_new_number() {
        let mut last = 0u64;
        let mut a = OneList::default();
        let mut b = OneList::default();
        a.mark(true, &mut last);
        assert_eq!((a.yes, a.number), (true, 1));
        a.mark(true, &mut last);
        assert_eq!(a.number, 1, "a tree that is already marked keeps its number");
        b.mark(true, &mut last);
        assert_eq!(b.number, 2);
        b.mark(false, &mut last);
        assert!(!b.yes);
        assert_eq!(b.number, 2);
    }

    #[test]
    fn tested_in_carries_its_groups() {
        let g = group_small();
        let t = TestedIn::new(&g);
        assert_eq!(t.groups().len(), 1);
        assert_eq!(TestedIn::with_two(&g, &g).groups().len(), 2);
        assert_eq!(no_sized_group().groups().len(), 0);
    }

    #[test]
    fn pow2_and_stage_cube_bits() {
        assert_eq!(pow2_at_least(0), 1);
        assert_eq!(pow2_at_least(1), 1);
        assert_eq!(pow2_at_least(2), 2);
        assert_eq!(pow2_at_least(3), 4);
        assert_eq!(pow2_at_least(5), 8);
        assert_eq!(pow2_at_least(1 << 20), 1 << 20);

        let mut g = group_small();
        g.k = 4;
        g.main.ell = 16;
        assert_eq!(stage_cube_bits(&g), 8);
        g.h = 2;
        g.mask = CodeSize { name: String::new(), log_n: 4, ell: 8, r: 1, over_e: false };
        assert_eq!(stage_cube_bits(&g), 9);
    }

    #[test]
    fn solve_stages_carries_the_sizes_from_stage_to_stage() {
        let mut s = goldilocks(1);
        s.samples = 1;
        let first = GroupSize {
            name: String::from("test"),
            main: CodeSize { name: String::from("test"), log_n: 4, ell: 16, r: 4, over_e: false },
            k: 2,
            ..GroupSize::default()
        };
        let choice = [
            StageChoice { k: 1, h: 0, log_n: 4, mask_log_n: 4 },
            StageChoice { k: 0, h: 0, log_n: 6, mask_log_n: 6 },
        ];
        let mut p = Plan::new(s);
        let st = solve_stages(&mut p, &first, 8, &choice);
        assert!(!p.refused(), "{}", p.why());
        assert_eq!(st.len(), 3);
        assert_eq!(st[0].g, first);
        assert_eq!(st[0].t, 8);

        // Stage 2: ell = 16 / 2 = 8; carried = 2 * 0 + 4 + 2 * 0 = 4;
        // mask ell = max(pow2(4 + 1 + 1 - 1), pow2(2 * 1 + 1 - 0)) = max(8, 4) = 8;
        // r_ood = 8 - 4 = 4.
        assert_eq!(st[1].g.k, 1);
        assert_eq!(st[1].g.h, 0);
        assert_eq!(st[1].g.main.log_n, 4);
        assert_eq!(st[1].g.main.ell, 8);
        assert_eq!(st[1].g.mask.log_n, 4);
        assert_eq!(st[1].g.mask.ell, 8);
        assert_eq!(st[1].r_ood, 4);
        assert!(st[1].t > 0);

        // Stage 3 is the last: k = h = 0, ell = 8. Its mask has room for
        // 2 * 8 + 3 * t2 symbols and the pad, rounded up to a power of two.
        let t2 = st[1].t;
        let carried = 2 * st[1].g.mask.ell + t2 + 2 * t2;
        let mask_ell = pow2_at_least(carried + 1 + 1 - 1);
        assert_eq!(st[2].g.k, 0);
        assert_eq!(st[2].g.h, 0);
        assert_eq!(st[2].g.main.log_n, 6);
        assert_eq!(st[2].g.main.ell, 8);
        assert_eq!(st[2].g.mask.log_n, 6);
        assert_eq!(st[2].g.mask.ell, mask_ell);
        assert_eq!(st[2].r_ood, mask_ell - carried);
        assert!(st[2].t > 0);
    }

    #[test]
    fn solve_stages_refuses_choices_that_cannot_be_met() {
        let s = goldilocks(1);
        let first = GroupSize {
            name: String::from("test"),
            main: CodeSize { name: String::from("test"), log_n: 4, ell: 16, r: 4, over_e: false },
            k: 2,
            ..GroupSize::default()
        };
        let mut p = Plan::new(s.clone());
        let st = solve_stages(&mut p, &first, 8, &[]);
        assert_eq!(st.len(), 1);
        assert_eq!(
            p.why(),
            "test: a proximity test folds at its first stage and has a last stage"
        );

        let mut no_fold = first.clone();
        no_fold.k = 0;
        let mut p = Plan::new(s.clone());
        let st = solve_stages(
            &mut p,
            &no_fold,
            8,
            &[StageChoice { k: 1, h: 0, log_n: 4, mask_log_n: 4 }],
        );
        assert_eq!(st.len(), 1);
        assert_eq!(
            p.why(),
            "test: a proximity test folds at its first stage and has a last stage"
        );

        // The last of two stages must have k = 0.
        let mut p = Plan::new(s.clone());
        let st = solve_stages(
            &mut p,
            &first,
            8,
            &[
                StageChoice { k: 1, h: 0, log_n: 4, mask_log_n: 4 },
                StageChoice { k: 1, h: 0, log_n: 4, mask_log_n: 4 },
            ],
        );
        // Stage 2 was accepted before stage 3's choice was refused.
        assert_eq!(st.len(), 2);
        assert_eq!(
            p.why(),
            "test, stage 3: a middle stage has 1 <= k and h <= k, the last stage k = h = 0"
        );

        // A middle stage must have k >= 1.
        let mut p = Plan::new(s.clone());
        let st = solve_stages(
            &mut p,
            &first,
            8,
            &[
                StageChoice { k: 0, h: 0, log_n: 4, mask_log_n: 4 },
                StageChoice { k: 0, h: 0, log_n: 4, mask_log_n: 4 },
            ],
        );
        assert_eq!(st.len(), 1);
        assert!(p.why().ends_with("a middle stage has 1 <= k and h <= k, the last stage k = h = 0"));

        // h > k.
        let mut p = Plan::new(s);
        let st = solve_stages(
            &mut p,
            &first,
            8,
            &[
                StageChoice { k: 1, h: 2, log_n: 4, mask_log_n: 4 },
                StageChoice { k: 0, h: 0, log_n: 4, mask_log_n: 4 },
            ],
        );
        assert_eq!(st.len(), 1);
        assert!(p.why().ends_with("a middle stage has 1 <= k and h <= k, the last stage k = h = 0"));
    }

    #[test]
    fn table_analysis_reads_distances_in_positions() {
        let s = Setting::goldilocks();
        let t = TableSize {
            code: CodeSize { name: String::from("t"), log_n: 10, ell: 512, r: 1, over_e: false },
            v: 8,
            answers: 1,
            distances: TableDistances { radius: 256, later_radius: 128, m_once: 0, m_later: 0 },
        };
        let a = analysis_table(&s, &t);
        assert!(!a.once.bad());
        assert!(!a.later.bad());
        assert!(!a.once.from_m);
        assert!(!a.later.from_m);
        // n = 1024, so 256 / 1024 = 1/4 and 128 / 1024 = 1/8.
        let quarter = Bound::ratio(&Big::from_u64(256), &Big::from_u64(1024));
        let eighth = Bound::ratio(&Big::from_u64(128), &Big::from_u64(1024));
        assert!(real_eq(&a.once.delta.lo, &quarter.lo));
        assert!(real_eq(&a.once.delta.hi, &quarter.hi));
        assert!(real_eq(&a.later.delta.lo, &eighth.lo));
        assert!(real_eq(&a.later.delta.hi, &eighth.hi));
    }

    #[test]
    fn table_analysis_reads_integers_m() {
        let s = Setting::goldilocks();
        let t = TableSize {
            code: CodeSize { name: String::from("t"), log_n: 10, ell: 512, r: 1, over_e: false },
            v: 8,
            answers: 1,
            distances: TableDistances { radius: 0, later_radius: 0, m_once: 5, m_later: 4 },
        };
        let a = analysis_table(&s, &t);
        assert!(a.once.from_m && a.later.from_m);
        assert_eq!((a.once.m, a.later.m), (5, 4));
        assert!(table_admitted(&t, &a));
        let later_six = TableAnalysis {
            once: analysis_table(&s, &t).once,
            later: johnson_code(&s, &t.code, 6),
        };
        assert!(!table_admitted(&t, &later_six));
    }

    #[test]
    fn table_admitted_checks_the_lists_and_the_record() {
        let s = Setting::goldilocks();
        let mut t = TableSize {
            code: CodeSize { name: String::from("t"), log_n: 10, ell: 512, r: 1, over_e: false },
            v: 8,
            answers: 1,
            distances: TableDistances { radius: 256, later_radius: 128, m_once: 0, m_later: 0 },
        };
        assert!(table_admitted_of(&s, &t));
        t.answers = 0;
        assert!(!table_admitted_of(&s, &t));
        t.answers = 1;
        t.distances.later_radius = 256;
        assert!(table_admitted_of(&s, &t));
    }

    #[test]
    fn table_fold_error_sums_the_variables_and_the_list_term() {
        // card_E = 2: mca = 1/2, field_error(v) = v/2.
        let s = Setting { p: Big::from_u64(2), degree: 1, ..Setting::default() };
        let t = TableSize { v: 2, ..TableSize::default() };
        let at = Proximity {
            agree: Bound::from_u64(1),
            delta: Bound::from_u64(0),
            eta: Bound::default(),
            m: 3,
            from_m: true,
            source: CountSource::Third,
            count: Bound::from_u64(1),
            list: Big::from_u64(1),
        };
        // 2 * (1/2) + 1 * (2/2) = 2.
        assert!(real_eq(&table_fold_error(&s, &t, &at).error(), &Real::from_u64(2)));
        let empty = TableSize { v: 0, ..TableSize::default() };
        // No variable: only list * field_error(0) = 0.
        assert!(real_eq(&table_fold_error(&s, &empty, &at).error(), &Real::from_u64(0)));
    }

    #[test]
    fn size_recorded_table_finds_the_cap_or_reports_none() {
        let s = goldilocks(1);
        let mut t = TableSize {
            code: CodeSize { name: String::from("t"), log_n: 10, ell: 512, r: 1, over_e: false },
            v: 8,
            answers: 1,
            distances: TableDistances::default(),
        };
        assert!(size_recorded_table(&s, &mut t, 1, 5));
        // The batching term grows like m^5, so the largest m is far below the cap; the later test
        // drops the record's condition, which is far smaller, so it keeps the one-time m.
        assert!(t.distances.m_once >= 3);
        assert!(t.distances.m_once < LARGEST_M_LIMIT);
        assert_eq!(t.distances.m_later, t.distances.m_once);
        assert!(table_admitted_of(&s, &t));

        let hard = goldilocks(100_000);
        let mut t = TableSize {
            code: CodeSize { name: String::from("t"), log_n: 10, ell: 512, r: 1, over_e: false },
            v: 8,
            answers: 1,
            distances: TableDistances::default(),
        };
        assert!(!size_recorded_table(&hard, &mut t, 1, 5));
        assert_eq!(t.distances.m_once, 0);
        assert_eq!(t.distances.m_later, 0);
    }

    #[test]
    fn priced_table_states_the_distances_and_test() {
        let t = TableSize {
            code: CodeSize { name: String::from("t"), log_n: 10, ell: 512, r: 1, over_e: false },
            v: 9,
            answers: 2,
            distances: TableDistances { radius: 256, later_radius: 128, m_once: 0, m_later: 0 },
        };
        let p = priced_table(&t, TableTest::Link);
        assert!(p.said);
        assert_eq!(p.test, TableTest::Link);
        assert_eq!((p.v, p.answers), (9, 2));
        assert_eq!(p.code, PricedCode { log_n: 10, ell: 512, r: 1 });
        assert_eq!(p.distances, t.distances);
    }

    #[test]
    fn in_plan_analyses_reject_with_the_where_label() {
        let s = goldilocks(1);
        let mut p = Plan::new(s.clone());
        let bad = GroupSize { h: 1, ..group_small() };
        let a = analysis_group_in_plan(&mut p, "fold", &bad);
        assert!(a.bad());
        assert_eq!(p.why(), "fold: mask rows without a mask code");

        let mut p = Plan::new(s);
        let t = TableSize {
            code: CodeSize { name: String::from("t"), log_n: 10, ell: 512, r: 1, over_e: false },
            v: 8,
            answers: 1,
            distances: TableDistances { radius: 256, later_radius: 1000, m_once: 0, m_later: 0 },
        };
        let a = analysis_table_in_plan(&mut p, "record", &t);
        assert!(a.later.bad());
        assert_eq!(p.why(), "record: the table's distances are not admitted");
        assert!(!table_admitted_of(&p.set, &t));
    }

    #[test]
    fn plan_positions_reads_the_plan_scope() {
        let mut s = goldilocks(3);
        s.set_work(ErrorKind::Query, Scope::Request, 0);
        let mut p = Plan::new(s);
        let half = Bound::ratio(&Big::from_u64(1), &Big::from_u64(2));
        assert_eq!(plan_positions(&p, &half, &Bound::from_u64(0)), 3);
        assert_eq!(plan_positions_default(&p, &half), 3);
        p.begin_scope(Scope::Shared);
        assert_eq!(plan_positions_default(&p, &half), 3);
    }

    #[test]
    fn a_round_can_be_built_by_hand_into_a_plan() {
        // The hand-made overload of close returns the round, which plan_* emitters then fill.
        let mut p = Plan::new(goldilocks(1));
        {
            let r = p.close_handmade(
                crate::numbers::round_names::R_BAT,
                crate::numbers::setting::RoundKind::Algebraic,
                ErrorKind::Field,
                &Bound::from_u64(0),
                crate::numbers::plan::Priced::AsSaid,
            );
            r.rows = 4;
        }
        let plan = p.finish();
        assert!(plan.holds());
        assert_eq!(plan.rounds.len(), 1);
        assert_eq!(plan.rounds[0].rows, 4);
        assert_eq!(plan.rounds[0].kind, crate::numbers::setting::RoundKind::Algebraic);
    }

    #[test]
    fn plan_open_rejects_a_marked_tree_read_twice_or_in_another_chain() {
        let mut last = 0u64;
        let mut tr = TreeSize {
            name: String::from("mask"),
            log_n: 4,
            leaf_bytes: 16,
            ..TreeSize::default()
        };
        tr.one_list.mark(true, &mut last);
        let mut p = Plan::new(Setting::goldilocks());
        plan_open(&mut p, "loc", &tr, 3);
        assert!(!p.refused(), "{}", p.why());
        plan_open(&mut p, "base", &tr, 3);
        assert_eq!(
            p.why(),
            "base: the tree mask holds the mask of one step and is opened at a second list"
        );

        let mut other = TreeSize { ..tr.clone() };
        other.from_another_chain = true;
        let mut q = Plan::new(Setting::goldilocks());
        plan_open(&mut q, "loc", &other, 3);
        assert_eq!(
            q.why(),
            "loc: the tree mask holds the mask of one step and is read in another chain"
        );
    }
}

#[cfg(test)]
mod cpp_parity_tests {
    //! The C++ tests' known values (`blocks/numbers/tests/numbers_test.cpp:192-223, 362-406`).
    use super::*;
    use crate::numbers::codes::hidden_positions;

    fn m61() -> Setting {
        Setting {
            field_name: String::from("2^61 - 1"),
            p: Big::sub(&Big::two_to(61), &Big::from_u64(1)),
            circle: true,
            ..Setting::default()
        }
    }

    fn lone(s: &Setting, log_n: u32, ell: u64, r: u64) -> GroupSize {
        let mut shape = GroupSize::default();
        shape.main.log_n = log_n;
        shape.main.ell = ell;
        shape.main.r = r;
        size_group(s, Scope::Request, &shape, &GroupLoad::default())
    }

    #[test]
    fn known_sizes_under_m61_match_the_cpp_test() {
        let s = m61();
        let l = lone(&s, 23, 1 << 22, 0);
        let h = lone(&s, 19, 1 << 16, 0);
        let a = |g: &GroupSize| analysis_group(&s, g).at.m;
        assert_eq!(a(&l), 73);
        assert_eq!(a(&h), 84);
        assert_eq!(a(&lone(&s, 20, 1 << 17, 0)), 73);
        assert_eq!(a(&lone(&s, 16, 1 << 12, 0)), 104);
        assert_eq!(a(&lone(&s, 11, 1 << 7, 0)), 209);

        // With CLOSENESS work 20 in the request scope.
        let mut w = s.clone();
        w.set_work(ErrorKind::Closeness, Scope::Request, 20);
        let lw = lone(&w, 23, 1 << 22, 0);
        let hw = lone(&w, 19, 1 << 16, 0);
        assert_eq!(analysis_group(&w, &lw).at.m, 1189);
        assert_eq!(analysis_group(&w, &hw).at.m, 1366);

        // The edge of the slack: m holds, m + 1 does not.
        let load = GroupLoad::default();
        for (x, g) in [(&s, &l), (&s, &h), (&w, &lw)] {
            let mut shape = GroupSize::default();
            shape.main = g.main.clone();
            let m = analysis_group(x, g).at.m;
            assert!(group_holds(x, Scope::Request, &group_of_m(&shape, m), &load));
            assert!(!group_holds(x, Scope::Request, &group_of_m(&shape, m + 1), &load));
        }
    }

    #[test]
    fn known_table_values_match_the_cpp_test() {
        for s in [m61(), Setting::goldilocks()] {
            let t = TableSize {
                code: CodeSize {
                    name: String::new(),
                    log_n: 33,
                    ell: 402653184,
                    r: 44040191,
                    over_e: false,
                },
                v: 11,
                answers: 1,
                distances: TableDistances {
                    radius: 1 << 31,
                    later_radius: 1 << 31,
                    m_once: 0,
                    m_later: 0,
                },
            };
            assert!(table_admitted_of(&s, &t));
            let a = analysis_table(&s, &t);
            assert_eq!(a.once.source, CountSource::Third);
            // Eleven proximity terms of (2^31 + 1) / |E| and a list term (numbers_test.cpp:526-528).
            let fold = table_fold_error(&s, &t, &a.once);
            let inner = Big::add(&Big::two_to(31), &Big::from_u64(1));
            let num = Big::add(&Big::mul(&Big::from_u64(11), &inner), &Big::from_u64(11));
            let by_hand = Bound::ratio(&num, &s.card_e());
            let slack = Real::add(&Real::from_u64(1), &Real::two_to(-150), Dir::Up);
            assert!(fold.hi <= Real::mul(&by_hand.hi, &slack, Dir::Up));
            assert!(by_hand.lo <= fold.hi);
        }
    }

    #[test]
    fn stage_invariants_match_the_cpp_test() {
        for s in [m61(), Setting::goldilocks()] {
            let x = &s;
            let mut p = Plan::new(s.clone());
            let mut g = GroupSize {
                name: String::from("g"),
                main: CodeSize { name: String::new(), log_n: 23, ell: 1 << 22, r: 341, over_e: false },
                mask: CodeSize { name: String::new(), log_n: 17, ell: 1 << 13, r: 341, over_e: true },
                k: 8,
                ..GroupSize::default()
            };
            g = size_group(x, Scope::Request, &g, &GroupLoad::default());
            let choice = [
                StageChoice { k: 5, h: 3, log_n: 20, mask_log_n: 16 },
                StageChoice { k: 5, h: 3, log_n: 16, mask_log_n: 16 },
                StageChoice { k: 5, h: 3, log_n: 13, mask_log_n: 13 },
                StageChoice { k: 0, h: 0, log_n: 15, mask_log_n: 15 },
            ];
            let t1 = plan_positions_default(&p, &analysis_group(x, &g).at.agree);
            let st = solve_stages(&mut p, &g, t1, &choice);
            assert!(!p.refused(), "{}", p.why());
            assert_eq!(st.len(), 5);
            for i in 0..st.len() - 1 {
                let a = &st[i].g;
                let b = &st[i + 1].g;
                assert_eq!(a.main.ell, b.main.ell << b.k, "stage {}", i + 2);
                assert_eq!(
                    b.mask.ell << b.h,
                    2 * a.mask.ell + a.main.r + 2 * a.mask.r + st[i + 1].r_ood,
                    "stage {}",
                    i + 2
                );
                assert!(st[i + 1].r_ood >= x.samples as u64);
                assert!(b.mask.ell.is_power_of_two() && (b.k == 0 || b.mask.ell >= 2 * b.k as u64 + 1 - b.h as u64));
                assert!(hidden_positions(x, &b.main) >= st[i + 1].t);
                assert!(hidden_positions(x, &b.mask) >= st[i + 1].t);
                assert!(b.main.dim(x) <= b.main.n() && b.mask.dim(x) <= b.mask.n());
                assert!(b.mask.log_n <= b.main.log_n);
            }
        }
    }
}
