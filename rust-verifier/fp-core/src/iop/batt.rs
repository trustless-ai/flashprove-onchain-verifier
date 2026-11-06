//! BATT, batching claims on the committed matrix, ported from `blocks/iop/batt.h`
//! (lines 40-169, the verifier side). The heavy sumcheck of the prover is a caller-supplied
//! `SumcheckProver`; no verifier code reaches it.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

use super::hp::Weight;
use super::mask::{MaskLedger, MaskTerm};
use super::psc::{psc_verify, PscOutput};
use super::summand::{SumClaim, Summand};
use super::tensor::Tensor;
use crate::chain::rounds::VerifierRounds;
use crate::field::ext::E;
use crate::field::mle::eq_eval;
use crate::hash::calls::HashCalls;
use crate::numbers::round_names::R_BAT_SIGMA;

/// `< g (x) eq(psi, .), M > + <masks> = target` (`TensorRow`, batt.h:40-46).
pub struct TensorRow {
    pub g: Vec<Tensor>,
    pub psi: Vec<E>,
    pub masks: Vec<MaskTerm<E>>,
    pub target: E,
}

/// The number of scalars one BATT sends (`batt_masks`, batt.h:50).
pub fn batt_masks(k_col: u32) -> usize {
    1 + 2 * k_col as usize
}

/// PSC's input from the claims and x (`BattClaim`, batt.h:57-62).
pub struct BattClaim {
    pub chi: Vec<E>,
    pub psi: Vec<Vec<E>>,
    pub claim: SumClaim,
    pub summand: Summand,
}

/// `batt_k_col` (batt.h:63-66).
pub fn batt_k_col(rows: &[TensorRow]) -> u32 {
    assert!(
        !rows.is_empty() && !rows[0].psi.is_empty(),
        "BATT: no row, or a matrix of one column"
    );
    rows[0].psi.len() as u32
}

/// `batt_claim` (batt.h:67-91).
pub fn batt_claim(rows: &mut [TensorRow], x: E) -> BattClaim {
    let k_col = batt_k_col(rows);
    let mut b = BattClaim {
        chi: Vec::new(),
        psi: Vec::new(),
        claim: SumClaim { vars: Vec::new(), masks: Vec::new(), target: E::zero() },
        summand: Summand {
            shown: 0,
            kept: 0,
            degree: 0,
            at: Box::new(|_: &[E], _: &[E]| Vec::new()),
        },
    };
    let row_vars = rows[0].g[0].vars();
    let mut power = E::one();
    for r in rows.iter_mut() {
        assert!(r.psi.len() as u32 == k_col, "BATT: the rows' points differ in length");
        assert!(!r.g.is_empty(), "BATT: a row without weights");
        for t in &r.g {
            assert!(
                t.vars() == row_vars,
                "BATT: not all weights have the same number of row variables"
            );
        }
        b.chi.push(power);
        b.claim.target = b.claim.target + power * r.target;
        for m in core::mem::take(&mut r.masks) {
            b.claim.masks.push(MaskTerm { slot: m.slot, coeff: power * m.coeff });
        }
        b.psi.push(r.psi.clone());
        power = power * x;
    }
    b.claim.vars = vec![Weight::plain(3); k_col as usize];
    let chi = b.chi.clone();
    let psi = b.psi.clone();
    b.summand.shown = 0;
    b.summand.kept = rows.len() as u32;
    b.summand.degree = 0;
    b.summand.at = Box::new(move |point: &[E], _y: &[E]| {
        let mut a = vec![E::zero()];
        for j in 0..chi.len() {
            a.push(chi[j] * eq_eval(&psi[j], point, k_col as usize));
        }
        a
    });
    b
}

/// PSC's output claim as a `TensorRow` (`batt_row`, batt.h:97-108).
pub fn batt_row(rows: &[TensorRow], out: PscOutput) -> TensorRow {
    let mut r = TensorRow { g: Vec::new(), psi: out.point, masks: out.row_masks, target: out.row_target };
    for t in &out.row_maps {
        for g in &rows[t.map as usize].g {
            let mut g = g.clone();
            g.scalar = g.scalar * t.coeff;
            r.g.push(g);
        }
    }
    r
}

/// Draws x (round `BAT-sigma`) (`batt_draw`, batt.h:120-125).
pub fn batt_draw(
    ch: &mut VerifierRounds<'_, '_, '_>,
    rows: usize,
    calls: &mut HashCalls,
) -> E {
    let mut from = ch.close_algebraic(R_BAT_SIGMA, calls);
    from.require_rows(rows as u64);
    from.draw(calls)
}

/// The verifier's BATT (`batt_verify`, batt.h:161-169).
pub fn batt_verify(
    ch: &mut VerifierRounds<'_, '_, '_>,
    mut rows: Vec<TensorRow>,
    ledger: &mut MaskLedger,
    calls: &mut HashCalls,
) -> (TensorRow, bool) {
    let k_col = batt_k_col(&rows);
    let n = rows.len();
    let x = batt_draw(ch, n, calls);
    let b = batt_claim(&mut rows, x);
    let mut out = PscOutput {
        point: Vec::new(),
        row_masks: Vec::new(),
        row_maps: Vec::new(),
        row_target: E::zero(),
        ends: Vec::new(),
    };
    if !psc_verify(ch, b.claim, &b.summand, ledger.take_n(batt_masks(k_col)), &mut out, calls) {
        return (
            TensorRow { g: Vec::new(), psi: Vec::new(), masks: Vec::new(), target: E::zero() },
            false,
        );
    }
    let r = batt_row(&rows, out);
    let ok = ch.ok();
    (r, ok)
}

/// A claim on one row of the matrix, for callers that build the input by hand.
pub fn tensor_row(g: Vec<Tensor>, psi: Vec<E>, target: E) -> TensorRow {
    TensorRow { g, psi, masks: Vec::new(), target }
}
