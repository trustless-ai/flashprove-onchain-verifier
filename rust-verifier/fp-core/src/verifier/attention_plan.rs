//! The rounds of the attention sub-proof on the proof's plan, ported from
//! `prover/attn/plan_rounds.h`.
//!
//! Prover and verifier include the C++ file and fill [`AttentionRounds`] from their own shape.
//! The emitters are the Rust `plan_*` functions of [`crate::numbers::blocks`].

use alloc::vec::Vec;

use crate::numbers::blocks::{
    plan_bat_sigma, plan_psc, plan_scalars, plan_zero, PscSize,
};
use crate::numbers::plan::Plan;

/// `attention_sc3(nv, pairs)`: an SC3 over `nv` variables and `pairs` pairs, degree 3 per round.
pub fn attention_sc3(nv: u32, pairs: u32) -> PscSize {
    PscSize { degree: vec![4; nv as usize], degree_y: 2, values: 2 * pairs, with_y: true }
}

/// `attention_scd(lt, lgk, pairs, Lam)`: the SCD's rounds.
pub fn attention_scd(lt: u32, lgk: u32, pairs: u32, lam: u32) -> PscSize {
    let mut degree = vec![3; lt as usize];
    degree.extend(core::iter::repeat(lt + 3).take(lgk as usize));
    degree.extend(core::iter::repeat(lt + 2).take(lt as usize));
    let _ = lam; // Lam enters through values, not a round
    PscSize { degree, degree_y: lt + 1, values: lam + pairs * lt, with_y: true }
}

/// The rounds of the attention sub-proof (`struct AttentionRounds`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AttentionRounds {
    pub lt: u32,
    pub lgk: u32,
    /// `NP = Lam * HA`.
    pub pairs: u32,
    pub lam: u32,
    /// Lookup segments RM, RD present in calls of kind KR; 3 scalars each.
    pub plane_messages: u32,
    /// For each lookup segment FM, FD that is present, in the order of the calls: (variables, pieces).
    pub score: Vec<(u32, u32)>,
    /// Variables of the SC3 for Z o, the value product's two, q k at the index, the index bits.
    pub e: u32,
    pub value_m: u32,
    pub value_d: u32,
    pub attained: u32,
    pub bits: u32,
    /// Batched by the last round: the sub-proof's linear claims and its range check's equations.
    pub rows: u64,
}

/// `plan_attention_own`.
pub fn plan_attention_own(p: &mut Plan, where_: &str, x: &AttentionRounds) {
    if x.plane_messages != 0 {
        plan_scalars(p, "plane values", where_, 3 * x.plane_messages as u64);
    }
    for &(nv, np) in &x.score {
        plan_scalars(p, "plane values and the scores' sum", where_, 7);
        plan_psc(p, &format!("{}, scores", where_), &attention_sc3(nv, np));
    }
    plan_scalars(p, "sums, index bits, remainders", where_, 5 + x.lt as u64 + 2);
    plan_psc(p, &format!("{}, Z o", where_), &attention_sc3(x.e, x.pairs));
    plan_bat_sigma(p, &format!("{}, numerator and denominator", where_), 2);
    plan_scalars(p, "the value product's two sums", where_, 2);
    plan_psc(
        p,
        &format!("{}, value product, off the diagonal", where_),
        &attention_sc3(x.value_m, x.pairs),
    );
    plan_psc(
        p,
        &format!("{}, value product, diagonal", where_),
        &attention_sc3(x.value_d, x.pairs),
    );
    plan_zero(
        p,
        &format!("{}, the maximum is attained; the index bits are bits", where_),
        2 * x.lgk + 2 * x.lt + 4,
    );
    plan_scalars(p, "the maxima at the point", where_, x.pairs as u64);
    plan_bat_sigma(p, &format!("{}, maxima", where_), x.pairs as u64);
    plan_psc(
        p,
        &format!("{}, q k at the index", where_),
        &attention_sc3(x.attained, x.pairs),
    );
    plan_bat_sigma(p, &format!("{}, keys at the index", where_), x.pairs as u64);
    plan_psc(
        p,
        &format!("{}, the key at the index", where_),
        &attention_scd(x.lt, x.lgk, x.pairs, x.lam),
    );
    plan_bat_sigma(p, &format!("{}, index bits", where_), x.pairs as u64);
    plan_psc(
        p,
        &format!("{}, index bits", where_),
        &attention_sc3(x.bits, x.pairs),
    );
}

/// `plan_attention_end`: after the sub-proof's last message.
pub fn plan_attention_end(p: &mut Plan, where_: &str, x: &AttentionRounds) {
    plan_bat_sigma(p, &format!("{}, all rows", where_), x.rows);
}

use alloc::format;
use alloc::vec;
