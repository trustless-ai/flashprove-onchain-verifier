//! A layer sub-proof's own planning rounds, ported from `prover/prover/plan_rounds.h`:
//! `LayerRounds`, `plan_product_layer`, `plan_token_sumcheck` and `plan_layer_own`. Prover and
//! verifier compile these; the verifier's plan uses them in `vf_layers_plan.inc`.
//!
//! "Bits of n": log2 of n. A sumcheck (`psc` in identifiers) "shows" the values that it sends,
//! masked, at its last point. TSC(P_V), TSC(zt): sumchecks over the token bits, at the norms'
//! token point and at zt. R: a norm's scaled reciprocal. sc: a routed layer's score. Selector:
//! one entry per expert.

use alloc::format;
use alloc::vec;

use crate::numbers::blocks::{
    plan_bat_sigma, plan_join, plan_line, plan_psc, plan_scalars, plan_zero, PscSize,
};
use crate::numbers::plan::Plan;

/// The sizes that `layer_setup` (prover) and `vf_layers_plan.inc` (verifier) fill and must agree
/// on (`LayerRounds`, plan_rounds.h:26-44).
#[derive(Clone, Debug)]
pub struct LayerRounds {
    /// Token bits.
    pub lt: u32,
    /// Bits of a block of features in a long read.
    pub ls: u32,
    /// Bits of the norm instances' number.
    pub l_ni: u32,
    /// Bits of the padded model width.
    pub l_pd: u32,
    /// Bits of the layers' number in the group.
    pub ll: u32,
    /// Bits of the padded hidden width.
    pub l_pf: u32,
    /// Bits of a routed expert's hidden width.
    pub l_fe: u32,
    /// Rounds of the batched inner-product sumcheck.
    pub lam_s: u32,
    /// Rounds of the merge of weight claims into one.
    pub lk_w: u32,
    /// Norm instances.
    pub ni: u64,
    /// For each instance: sums of limb products, row products, row values that TSC(P_V) shows.
    pub ns: u64,
    pub np: u64,
    pub no: u64,
    /// The call list has terms for the second token sumcheck, TSC(zt).
    pub with_terms: bool,
    /// R per instance; with routed experts sc and the selector's entries.
    pub shown_by_the_terms: u64,
    /// Values of never-sent vectors that the batched sumcheck shows: 1 + the routed layers.
    pub never_sent: u64,
    /// Weight claims, without the embedding's.
    pub weight_claims: u64,
    /// The group that also proves the embedding's claim.
    pub first_group: bool,
    /// The group has layers with routed experts.
    pub routed: bool,
}

impl Default for LayerRounds {
    /// The C++ member defaults (plan_rounds.h:28-43): `with_terms` is true.
    fn default() -> Self {
        LayerRounds {
            lt: 0,
            ls: 0,
            l_ni: 0,
            l_pd: 0,
            ll: 0,
            l_pf: 0,
            l_fe: 0,
            lam_s: 0,
            lk_w: 0,
            ni: 0,
            ns: 0,
            np: 0,
            no: 0,
            with_terms: true,
            shown_by_the_terms: 0,
            never_sent: 0,
            weight_claims: 0,
            first_group: false,
            routed: false,
        }
    }
}

/// `plan_product_layer` (plan_rounds.h:46-51).
pub fn plan_product_layer(p: &mut Plan, where_: &str, variables: u32) {
    let x = PscSize {
        degree: vec![3u32; variables as usize],
        degree_y: 2,
        values: 2,
        ..PscSize::default()
    };
    plan_psc(p, where_, &x);
    plan_line(p, where_);
}

/// `plan_token_sumcheck` (plan_rounds.h:52-57).
pub fn plan_token_sumcheck(
    p: &mut Plan,
    where_: &str,
    lt: u32,
    degree_y: u32,
    shown: u64,
) {
    plan_scalars(p, "claimed sum", where_, 1);
    let x = PscSize {
        degree: vec![3u32; lt as usize],
        degree_y,
        values: shown as u32,
        ..PscSize::default()
    };
    plan_psc(p, where_, &x);
}

/// `plan_layer_own` (plan_rounds.h:87-127): the rounds after a commit point that are the layer
/// sub-proof's own. The order must match the messages in `vf_layers_check.inc` and the steps in
/// `layer_prove.cuh`.
pub fn plan_layer_own(p: &mut Plan, where_: &str, x: &LayerRounds) {
    plan_zero(p, &format!("{}, the norms' token point", where_), x.lt);
    if x.first_group {
        plan_zero(p, &format!("{}, the embedding's point", where_), x.ls + x.lt);
        plan_zero(p, &format!("{}, the embedding's feature point", where_), x.l_pd - x.ls);
    }
    plan_scalars(p, "sums of limb products", where_, x.ns * x.ni);
    plan_bat_sigma(p, &format!("{}, limbs", where_), x.ns);
    if x.l_ni != 0 {
        plan_join(p, &format!("{}, norm instances", where_), x.l_ni);
    }
    plan_product_layer(p, &format!("{}, sums of squares", where_), x.l_ni + x.l_pd + x.lt);
    plan_scalars(p, "row products", where_, x.np * x.ni);
    plan_bat_sigma(p, &format!("{}, row products", where_), x.np * x.ni);
    plan_token_sumcheck(p, &format!("{}, row products", where_), x.lt, 2, x.no * x.ni);
    if x.with_terms {
        plan_token_sumcheck(p, &format!("{}, terms", where_), x.lt, 1, x.shown_by_the_terms);
        plan_bat_sigma(p, &format!("{}, start of the inner products", where_), 2);
    }
    {
        let s = PscSize {
            degree: vec![3u32; x.lam_s as usize],
            degree_y: 2,
            values: (2 + x.never_sent + x.weight_claims) as u32,
            ..PscSize::default()
        };
        plan_psc(p, &format!("{}, inner products", where_), &s);
    }
    plan_product_layer(p, &format!("{}, gated products", where_), x.ll + x.l_pf + x.lt);
    if x.routed {
        if x.ll > 1 {
            plan_join(p, &format!("{}, layers with routed experts", where_), x.ll - 1);
        }
        plan_product_layer(
            p,
            &format!("{}, routed gated products", where_),
            x.ll - 1 + x.l_fe + x.lt,
        );
    }
    if x.first_group {
        plan_scalars(p, "the embedding's value", where_, 1);
    }
    plan_bat_sigma(
        p,
        &format!("{}, weight claims", where_),
        x.weight_claims + if x.first_group { 1 } else { 0 },
    );
    {
        let m = PscSize {
            degree: vec![3u32; x.lk_w as usize],
            degree_y: 1,
            values: 1,
            ..PscSize::default()
        };
        plan_psc(p, &format!("{}, weight claims", where_), &m);
    }
}
