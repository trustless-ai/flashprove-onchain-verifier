//! The output head's own planning rounds, ported from `prover/head/plan_rounds.h`:
//! `HeadRounds`, `plan_head_own` and `plan_head_end`, and the token sumcheck's entry
//! (`plan_token_sum`, `prover/hiding/token_plan.h`) that they use. The verifier's plan uses them
//! in `vf_output_head_plan.inc`.
//!
//! The sub-proof is one segment of a request's proof; `req_plan()` plans its messages and the next
//! token's round. The callers plan what follows each of its three commit points: 0, after the
//! cells: the sub-proof's lookup, then `plan_head_own()`; 1, after the reads: the approximate
//! range check's matrix; 2, after its digits: the range check's lookup on them, then
//! `plan_head_end()`.

use alloc::format;
use alloc::vec;

use crate::numbers::blocks::{
    plan_bat_sigma, plan_line, plan_psc, plan_scalars, plan_zero, PscSize,
};
use crate::numbers::plan::Plan;

/// The sizes of the head's rounds (`HeadRounds`, plan_rounds.h:26-33). Prover and verifier each
/// fill it from their own shape.
#[derive(Clone, Debug, Default)]
pub struct HeadRounds {
    /// Log2 of: token positions, padded features, weight columns.
    pub lt: u32,
    pub l_pd: u32,
    pub lk_w: u32,
    /// Of the norm: `2 * limbs - 1` sums of limb products; 7 row products of 4 row values with 5
    /// limbs, else 3 of 3.
    pub sums: u32,
    pub products: u32,
    pub row_values: u32,
    /// What the last round batches: the sub-proof's linear claims and its range check's equations.
    pub rows: u64,
}

/// The token sumcheck's rounds (`plan_token_sum`, token_plan.h:23-29): the claimed sum, a hidden
/// value sent masked, then its masked sumcheck under eq weights: `lt` rounds over `2^lt` token
/// positions, then `more` rounds over an index with equal weights. If `shown > 0`, a round in a
/// further variable Y and `shown` end values follow, then no challenge. `degree_in_y`: the
/// summand's degree in the maps whose end values are sent. A round polynomial omits its eq factor:
/// degree below 3, two scalars if `Setting::saved_coefficient`.
pub fn plan_token_sum(
    p: &mut Plan,
    where_: &str,
    lt: u32,
    shown: u32,
    degree_in_y: u32,
    more: u32,
) {
    plan_scalars(p, "token sum", where_, 1);
    let x = PscSize {
        degree: vec![3u32; (lt + more) as usize],
        degree_y: degree_in_y,
        values: shown,
        with_y: shown > 0,
    };
    plan_psc(p, where_, &x);
}

/// `plan_head_own` (plan_rounds.h:77-90): the final norm's rounds, then the logits' sumcheck.
pub fn plan_head_own(p: &mut Plan, where_: &str, x: &HeadRounds) {
    plan_zero(p, &format!("{}, the norm's point", where_), x.lt);
    plan_scalars(p, "sums of limb products", where_, x.sums as u64);
    plan_bat_sigma(p, &format!("{}, limbs", where_), x.sums as u64);
    // Sums squares over features (plain: equality weights at 1/2) and token positions.
    let layer = PscSize {
        degree: vec![3u32; (x.l_pd + x.lt) as usize],
        degree_y: 2,
        values: 2,
        ..PscSize::default()
    };
    plan_psc(p, &format!("{}, sum of squares", where_), &layer);
    plan_line(p, &format!("{}, sum of squares", where_));
    plan_scalars(p, "row products", where_, x.products as u64);
    plan_bat_sigma(p, &format!("{}, row products", where_), x.products as u64);
    plan_token_sum(p, &format!("{}, row products", where_), x.lt, x.row_values, 2, 0);
    plan_token_sum(p, &format!("{}, stream times reciprocal", where_), x.lt, 2, 2, 0);
    plan_token_sum(
        p,
        &format!("{}, activations times head", where_),
        x.lt,
        2,
        2,
        x.l_pd,
    );
}

/// `plan_head_end` (plan_rounds.h:93-102): the merge of the one claim on the weight table, which
/// sends the value that goes to the opening of the weights; then the round that batches `x.rows`.
pub fn plan_head_end(p: &mut Plan, where_: &str, x: &HeadRounds) {
    plan_bat_sigma(p, &format!("{}, merge", where_), 1);
    // Plain sums over the lkW column bits, round polynomials of degree 2 (PscSize::degree counts
    // their 3 coefficients, of which 2 are sent); one end value, in which the summand has degree 1.
    let merge = PscSize {
        degree: vec![3u32; x.lk_w as usize],
        degree_y: 1,
        values: 1,
        ..PscSize::default()
    };
    plan_psc(p, &format!("{}, merge", where_), &merge);
    plan_bat_sigma(p, &format!("{}, all rows", where_), x.rows);
}
