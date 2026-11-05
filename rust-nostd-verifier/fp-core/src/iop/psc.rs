//! PSC, the masked sumcheck, ported from `blocks/iop/psc.h` (lines 43-189, the verifier side).
//!
//! The C++ template over K is specialised to E, the challenge field of the verifier. The prover's
//! half needs a `SumcheckProver` and a prover channel; S2b-2 ports the verifier's rows and checks.

use alloc::vec;
use alloc::vec::Vec;

use super::hp::{hp_entries, hp_form, poly_at, Weight};
use super::mask::{MaskSlot, MaskTerm};
use super::summand::{PointClaim, SumClaim, Summand};
use crate::chain::rounds::VerifierRounds;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::round_names::{
    R_PSC_EPSILON, R_PSC_ROUND, R_PSC_VALUES, R_PSC_Y,
};

/// A kept map's term in PSC's output (`KeptTerm`, psc.h:43-47).
pub struct KeptTerm {
    pub map: u32,
    pub coeff: E,
}

/// The linear claims that PSC leaves (`PscOutput`, psc.h:51-60).
pub struct PscOutput {
    pub point: Vec<E>,
    pub row_masks: Vec<MaskTerm<E>>,
    pub row_maps: Vec<KeptTerm>,
    pub row_target: E,
    pub ends: Vec<PointClaim>,
}

/// The sizes that a plan needs (`PscSize`, blocks/numbers/blocks.h:570-575).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PscSize {
    pub degree: Vec<u32>,
    pub degree_y: u32,
    pub values: u32,
    pub with_y: bool,
}

/// The variables of the masked sumcheck (`psc_vars`, psc.h:64-71).
pub fn psc_vars(claim: &SumClaim, s: &Summand) -> Vec<Weight<E>> {
    assert!(
        (s.shown == 0) == (s.degree == 0),
        "psc: degree > 0 exactly if a map is shown"
    );
    assert!(
        s.shown > 0 || !claim.vars.is_empty(),
        "psc: nothing to sum over and nothing to show"
    );
    let mut vars = claim.vars.clone();
    if s.shown > 0 {
        vars.push(Weight::at_zero(s.degree + 1));
    }
    vars
}

/// The number of mask entries one PSC uses (`psc_masks`, psc.h:76-79).
pub fn psc_masks(claim: &SumClaim, s: &Summand) -> usize {
    hp_entries(&psc_vars(claim, s)) + s.shown as usize
}

/// The sizes that `plan_psc()` needs (`psc_size`, psc.h:87-94).
pub fn psc_size(claim: &SumClaim, s: &Summand) -> PscSize {
    let _ = psc_vars(claim, s);
    let mut x = PscSize { degree: Vec::new(), degree_y: s.degree, values: s.shown, with_y: s.shown > 0 };
    for v in &claim.vars {
        x.degree.push(v.d);
    }
    x
}

/// The output claims (`psc_rows`, psc.h:103-126).
pub fn psc_rows(
    claim: SumClaim,
    s: &Summand,
    vars: &[Weight<E>],
    fresh: Vec<MaskSlot>,
    eps: E,
    challenges: &[E],
    last: E,
    end_values: &[E],
) -> PscOutput {
    let mut out = PscOutput {
        point: challenges[..claim.vars.len()].to_vec(),
        row_masks: Vec::new(),
        row_maps: Vec::new(),
        row_target: E::zero(),
        ends: Vec::new(),
    };
    let a = (s.at)(&out.point, end_values);
    assert!(
        a.len() == 1 + s.kept as usize,
        "psc: Summand::at gives one coefficient for each kept map"
    );
    let form = hp_form(vars, challenges);
    let mut fresh = fresh.into_iter();
    for f in &form {
        out.row_masks.push(MaskTerm { slot: fresh.next().unwrap(), coeff: *f });
    }
    let mut psis = eps;
    for t in 0..vars.len() {
        psis = psis * poly_at(&vars[t].psi, challenges[t]);
    }
    for m in claim.masks {
        out.row_masks.push(MaskTerm { slot: m.slot, coeff: psis * m.coeff });
    }
    for i in 0..s.kept as usize {
        out.row_maps.push(KeptTerm { map: i as u32, coeff: eps * a[1 + i] });
    }
    out.row_target = last - eps * a[0];
    for j in 0..s.shown as usize {
        let mut e = PointClaim {
            point: out.point.clone(),
            masks: Vec::new(),
            value: end_values[j],
        };
        e.masks.push(MaskTerm { slot: fresh.next().unwrap(), coeff: challenges[challenges.len() - 1] });
        out.ends.push(e);
    }
    out
}

/// The verifier's PSC (`psc_verify`, psc.h:162-189). `fresh`: `psc_masks()` entries from a
/// `MaskLedger`. False if the channel rejected the proof; `out` is then worth nothing.
pub fn psc_verify(
    ch: &mut VerifierRounds<'_, '_, '_>,
    claim: SumClaim,
    s: &Summand,
    fresh: Vec<MaskSlot>,
    out: &mut PscOutput,
    calls: &mut HashCalls,
) -> bool {
    let vars = psc_vars(&claim, s);
    assert!(
        fresh.len() == hp_entries(&vars) + s.shown as usize,
        "psc: wrong number of fresh mask entries"
    );
    let k = claim.vars.len();

    let mut mu = E::zero();
    if !ch.recv_hiding_sum(&mut mu) {
        return false;
    }
    let eps = ch.close_epsilon(R_PSC_EPSILON, calls);

    let mut running = mu + eps * claim.target;
    let mut challenges: Vec<E> = Vec::new();
    for j in 0..vars.len() {
        let mut q = vec![E::zero(); vars[j].d as usize];
        for t in 0..vars[j].d as usize {
            if t != vars[j].fixed as usize && !ch.recv_e(&mut q[t]) {
                return false;
            }
        }
        vars[j].complete(&mut q, running);
        let g = {
            let mut draw = ch.close_algebraic(if j < k { R_PSC_ROUND } else { R_PSC_Y }, calls);
            if j < k {
                draw.draw(calls)
            } else {
                draw.draw_nonzero(calls)
            }
        };
        challenges.push(g);
        running = poly_at(&q, g);
    }
    let mut end_values = vec![E::zero(); s.shown as usize];
    for v in &mut end_values {
        if !ch.recv_e(v) {
            return false;
        }
    }
    if s.shown > 0 {
        ch.close_empty(R_PSC_VALUES, calls);
    }

    *out = psc_rows(claim, s, &vars, fresh, eps, &challenges, running, &end_values);
    ch.ok()
}
