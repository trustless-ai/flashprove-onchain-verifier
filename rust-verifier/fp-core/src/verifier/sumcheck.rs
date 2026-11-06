//! The sub-proofs' sumchecks, ported from `verifier/src/vf_sumcheck_psc.h`,
//! `vf_sumcheck_receive.h`, `vf_sumcheck_token.h` and `vf_sumcheck_attention.h`.
//!
//! A sumcheck proves that a sum equals a hidden value, given as an affine form ([`Aff`]). It runs
//! on a hiding polynomial `U + eps * G`: `U`'s sum and the rounds' coefficients are sent without
//! masks, and the round's missing coefficient is filled in by the running claim. The one test is
//! the linear claim that [`psc_row`] leaves; the caller adds it with [`HFork::lin`].
//!
//! C++ `blk::Weight<ExFieldAdapter>` becomes [`crate::iop::hp::Weight<E>`]; `blk::hp_form` and
//! `blk::poly_at` are the ported functions of `blocks/iop/hp.h` in [`crate::iop::hp`].

use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::iop::hp::{hp_form, poly_at, Weight};
use crate::refusal::{Refusal, Result};

use super::engine::{Aff, HFork};
use super::transcript::{tr_answer, tr_answer_not_zero, tr_empty, tr_read, tr_sum, RoundName, Tr};

/// One sumcheck's state (`struct Psc`).
#[derive(Clone, Debug, Default)]
pub struct Psc {
    /// What the sum must equal.
    pub start: Aff,
    /// `start` with each hidden value replaced by what was shown, `Aff::e` dropped.
    pub target: E,
    pub eps: E,
    /// The running claim of the masked sumcheck.
    pub claim: E,
    /// The number of its first slot and first mask entry.
    pub first: u32,
    /// The variables so far, in the order of the rounds.
    pub vars: Vec<Weight<E>>,
    /// Their challenges.
    pub r: Vec<E>,
    /// The round in the further variable Y has been run.
    pub ended: bool,
    pub row_made: bool,
    /// `start` is set.
    pub started: bool,
}

/// `pscBegin(tr, slot, target)`: reads `U`'s sum and draws eps.
pub fn psc_begin_target(
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    target: E,
    calls: &mut HashCalls,
) -> Result<Psc> {
    let mut p = Psc { target, first: *slot, ..Psc::default() };
    let mu = tr_sum(tr)?;
    p.eps = tr_answer(tr, RoundName::PscEpsilon, calls)?;
    p.claim = mu + p.eps * target;
    *slot += 1;
    Ok(p)
}

/// `pscBegin(F, tr, slot, C)`: the form that the sum must equal.
pub fn psc_begin(
    f: &HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    c: &Aff,
    calls: &mut HashCalls,
) -> Result<Psc> {
    let target = f.public_part(c)?;
    let mut p = psc_begin_target(tr, slot, target, calls)?;
    p.start = c.clone();
    p.started = true;
    Ok(p)
}

/// One round in a variable with the weight `w` (`pscRound`).
///
/// The message is the coefficients of the round polynomial `q`, lowest degree first, except
/// degree `w.fixed`, which the check `w(q) = claim` fills in.
fn psc_round(
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    p: &mut Psc,
    w: &Weight<E>,
    round: RoundName,
    nonzero: bool,
    calls: &mut HashCalls,
) -> Result<E> {
    let sent = tr_read(tr, w.d as usize - 1)?;
    let mut q = vec![E::zero(); w.d as usize];
    let mut i = 0usize;
    for t in 0..w.d as usize {
        if t != w.fixed as usize {
            q[t] = sent[i];
            i += 1;
        }
    }
    w.complete(&mut q, p.claim);
    let r = if nonzero {
        tr_answer_not_zero(tr, round, calls)?
    } else {
        tr_answer(tr, round, calls)?
    };
    p.claim = poly_at(&q, r);
    p.vars.push(w.clone());
    p.r.push(r);
    *slot += w.d - 1;
    Ok(r)
}

/// `pscEnds`: the round in Y, then `n` masked end values. Returns their first slot.
pub fn psc_ends(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    p: &mut Psc,
    degree_in_y: i32,
    n: u32,
    calls: &mut HashCalls,
) -> Result<u32> {
    if p.ended || degree_in_y < 1 || n < 1 {
        return Err(Refusal::internal(&alloc::format!("{}internal-psc-order", f.g)));
    }
    // With beta = 0 the end values would be sent without their masks.
    let beta = psc_round(
        tr,
        slot,
        p,
        &Weight::at_zero(degree_in_y as u32 + 1),
        RoundName::PscY,
        true,
        calls,
    )?;
    p.ended = true;
    let e = *slot;
    let v = tr_read(tr, n as usize)?;
    tr_empty(tr, RoundName::PscValues, calls)?;
    for j in 0..n {
        f.hide(e + j, v[j as usize], beta)?;
    }
    *slot += n;
    Ok(e)
}

/// `pscRow`: the one linear claim that a sumcheck leaves, as a form that must be 0.
pub fn psc_row(f: &mut HFork, p: &mut Psc, s0: E, kept: &Aff) -> Result<Aff> {
    if p.row_made || !p.started || p.vars.is_empty() {
        return Err(Refusal::internal(&alloc::format!("{}internal-psc-order", f.g)));
    }
    p.row_made = true;
    let form = hp_form(&p.vars, &p.r);
    let mut u = Aff::constant(E::zero() - (p.claim - p.eps * s0));
    for (i, x) in form.iter().enumerate() {
        f.hide(p.first + i as u32, E::zero(), E::zero() - E::one())?;
        u.add(&Aff::slot(p.first + i as u32), *x);
    }
    let mut pk = p.eps;
    for t in 0..p.vars.len() {
        pk = pk * poly_at(&p.vars[t].psi, p.r[t]);
    }
    let delta = Aff::constant(p.target) - p.start.clone();
    u.add(&delta, pk);
    u.add(kept, p.eps);
    Ok(u)
}

/// How a round sums its variable and the degree of its polynomial (`enum class RoundForm`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RoundForm {
    /// Degree 2; `c = (1 - z) g(0) + z g(1)`, and `g` omits the summand's equality factor.
    Eq2,
    /// Degree 2; `c = g(0) + g(1)`.
    Sum2,
    /// Degree 3; `c = g(0) + g(1)`.
    Sum3,
    /// Degree `degree`; `c = g(0) + g(1)`.
    Nodes,
    /// Degree `degree`; `c = (1 - z) g(0) + z g(1)`.
    Eq,
}

/// `roundValues(form, degree)`.
pub const fn round_values(form: RoundForm, degree: i32) -> u32 {
    match form {
        RoundForm::Sum3 => 3,
        RoundForm::Nodes | RoundForm::Eq => degree as u32,
        RoundForm::Eq2 | RoundForm::Sum2 => 2,
    }
}

/// `sumcheckSlots`.
pub const fn sumcheck_slots(form: RoundForm, rounds: i32, ends: u64, degree_in_y: i32, degree: i32) -> u64 {
    1 + rounds as u64 * round_values(form, degree) as u64 + degree_in_y as u64 + ends
}

/// `sumcheckSlotsDegrees`.
pub fn sumcheck_slots_degrees(degree: &[i32], ends: u64, degree_in_y: i32) -> u64 {
    let mut n = 1 + degree_in_y as u64 + ends;
    for &d in degree {
        n += d as u64;
    }
    n
}

/// `layerSlots(mu)`.
pub const fn layer_slots(mu: i32) -> u64 {
    sumcheck_slots(RoundForm::Eq2, mu, 2, 2, 0)
}

/// `roundIn`: one round of a sumcheck of the given form. Only `Eq2` and `Eq` read `z`; only
/// `Nodes` and `Eq` read `degree`.
pub fn round_in(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    form: RoundForm,
    p: &mut Psc,
    z: E,
    degree: i32,
    calls: &mut HashCalls,
) -> Result<E> {
    if p.ended {
        return Err(Refusal::internal(&alloc::format!("{}internal-psc-order", f.g)));
    }
    let equality = matches!(form, RoundForm::Eq2 | RoundForm::Eq);
    if matches!(form, RoundForm::Nodes | RoundForm::Eq) && (degree < 1 || degree > 64) {
        return Err(Refusal::internal(&alloc::format!("{}internal-psc-degree", f.g)));
    }
    let d = round_values(form, degree) + 1;
    let w = if equality { Weight::equality(z, d) } else { Weight::plain(d) };
    psc_round(tr, slot, p, &w, RoundName::PscRound, false, calls)
}

// ---------------------------------------------------------------------------------------------
// The token sumcheck (TSC), `vf_sumcheck_token.h`
// ---------------------------------------------------------------------------------------------

/// `TokenSumcheckState`.
pub struct TokenSumcheckState {
    /// The slot of `Cl`.
    pub s_cl: u32,
    /// The slot of the first end value.
    pub s_end: u32,
    /// The challenges, coordinate 0 first.
    pub r: Vec<E>,
    pub p: Psc,
    /// The claim from `psc_row`; empty unless the caller stores it.
    pub row_u: Aff,
}

/// `tscRounds`: `Cl`, the hiding polynomial's sum, and `lt` rounds of two scalars.
pub fn tsc_rounds(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    point: &[E],
    lt: i32,
    calls: &mut HashCalls,
) -> Result<TokenSumcheckState> {
    let mut o = TokenSumcheckState {
        s_cl: 0,
        s_end: 0,
        r: vec![E::zero(); lt as usize],
        p: Psc::default(),
        row_u: Aff::default(),
    };
    o.s_cl = f.claims_in(tr, slot, 1)?;
    o.p = psc_begin(f, tr, slot, &Aff::slot(o.s_cl), calls)?;
    for j in 0..lt as usize {
        o.r[j] = round_in(f, tr, slot, RoundForm::Eq2, &mut o.p, point[j], 0, calls)?;
    }
    Ok(o)
}

/// `tscIn`: the same, and the end.
pub fn tsc_in(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    point: &[E],
    lt: i32,
    shown: u32,
    degree_in_y: i32,
    calls: &mut HashCalls,
) -> Result<TokenSumcheckState> {
    let mut o = tsc_rounds(f, tr, slot, point, lt, calls)?;
    o.s_end = psc_ends(f, tr, slot, &mut o.p, degree_in_y, shown, calls)?;
    Ok(o)
}

/// `tscSlots(lt, shown, degreeInY, more)`.
pub const fn tsc_slots(lt: i32, shown: u64, degree_in_y: i32, more: i32) -> u64 {
    1 + sumcheck_slots(RoundForm::Eq2, lt + more, shown, degree_in_y, 0)
}

// ---------------------------------------------------------------------------------------------
// Attention's sumchecks, `vf_sumcheck_attention.h`
// ---------------------------------------------------------------------------------------------

/// SC3: rounds of degree 3 (`struct Degree3SumcheckState`).
pub struct Degree3SumcheckState {
    pub r: Vec<E>,
    pub s_end: u32,
    pub nb: usize,
    pub p: Psc,
    /// The one claim that the sumcheck leaves (`sc3Row`).
    pub row_u: Aff,
}

/// `sc3Slots(nv, nb)`.
pub const fn sc3_slots(nv: i32, nb: usize) -> u64 {
    sumcheck_slots(RoundForm::Sum3, nv, 2 * nb as u64, 2, 0)
}

/// `sc3In`.
pub fn sc3_in(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    nv: i32,
    nb: usize,
    start: &Aff,
    calls: &mut HashCalls,
) -> Result<Degree3SumcheckState> {
    let mut o = Degree3SumcheckState {
        r: vec![E::zero(); nv as usize],
        s_end: 0,
        nb,
        p: Psc::default(),
        row_u: Aff::default(),
    };
    o.p = psc_begin(f, tr, slot, start, calls)?;
    for j in 0..nv as usize {
        o.r[j] = round_in(f, tr, slot, RoundForm::Sum3, &mut o.p, E::zero(), 0, calls)?;
    }
    o.s_end = psc_ends(f, tr, slot, &mut o.p, 2, (2 * nb) as u32, calls)?;
    Ok(o)
}

/// `sc3A(o, b)`: the hidden end value `A_b(r)`.
pub fn sc3_a(o: &Degree3SumcheckState, b: usize) -> Aff {
    Aff::slot(o.s_end + (2 * b) as u32)
}

/// `sc3B(o, b)`: the hidden end value `B_b(r)`.
pub fn sc3_b(o: &Degree3SumcheckState, b: usize) -> Aff {
    Aff::slot(o.s_end + (2 * b + 1) as u32)
}

/// `sc3Row`: sets `o.row_u`. `w[b]` is `W_b(r)`; the summand is evaluated on the scalars sent.
pub fn sc3_row(f: &mut HFork, o: &mut Degree3SumcheckState, w: &[E], nm: &str) -> Result<()> {
    if w.len() != o.nb {
        return Err(Refusal::internal(&alloc::format!("internal-sc3-{}", nm)));
    }
    let mut s0 = E::zero();
    for b in 0..o.nb {
        s0 = s0
            + w[b]
                * f.shown(o.s_end + (2 * b) as u32)?
                * f.shown(o.s_end + (2 * b + 1) as u32)?;
    }
    o.row_u = psc_row(f, &mut o.p, s0, &Aff::default())?;
    Ok(())
}

/// SCD: round `j` has degree `d[j]` (`struct VariedDegreeSumcheckState`).
pub struct VariedDegreeSumcheckState {
    pub r: Vec<E>,
    pub s_end: u32,
    pub p: Psc,
    pub row_u: Aff,
}

/// `scdIn`.
pub fn scd_in(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    d: &[i32],
    degree_in_y: i32,
    n: usize,
    start: &Aff,
    calls: &mut HashCalls,
) -> Result<VariedDegreeSumcheckState> {
    let mut o = VariedDegreeSumcheckState {
        r: vec![E::zero(); d.len()],
        s_end: 0,
        p: Psc::default(),
        row_u: Aff::default(),
    };
    o.p = psc_begin(f, tr, slot, start, calls)?;
    for j in 0..d.len() {
        o.r[j] = round_in(f, tr, slot, RoundForm::Nodes, &mut o.p, E::zero(), d[j], calls)?;
    }
    o.s_end = psc_ends(f, tr, slot, &mut o.p, degree_in_y, n as u32, calls)?;
    Ok(o)
}
