//! BATT with its end value shown, ported from the verifier's side of
//! `blocks/iop/batt_shown.h` (lines 44-188). The prover's `BattShownSumcheck` and heavy sumcheck
//! are not ported.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

use super::batt::{batt_claim, batt_draw, batt_k_col, BattClaim, TensorRow};
use super::mask::{MaskLedger, MaskSlot, MaskTerm};
use super::psc::{psc_verify, PscOutput};
use super::summand::Summand;
use crate::chain::rounds::VerifierRounds;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;

/// The block's two claims (`BattShown`, batt_shown.h:44-48).
#[derive(Default)]
pub struct BattShown {
    pub row: TensorRow,
    pub own_masks: Vec<MaskTerm<E>>,
    pub own_target: E,
}

impl Default for TensorRow {
    fn default() -> Self {
        TensorRow { g: Vec::new(), psi: Vec::new(), masks: Vec::new(), target: E::zero() }
    }
}

/// `batt_shown_own_masks` (batt_shown.h:50).
pub fn batt_shown_own_masks(k_col: u32) -> usize {
    2 + 2 * k_col as usize
}

/// PSC's summand `S(X, y) = y` (`batt_shown_summand`, batt_shown.h:73-78).
pub fn batt_shown_summand() -> Summand {
    Summand {
        shown: 1,
        kept: 0,
        degree: 1,
        at: Box::new(|_p: &[E], y: &[E]| vec![y[0]]),
    }
}

/// `a_j = chi_j eq(psi_j, gamma)` (`batt_shown_scalars`, batt_shown.h:80-84).
pub fn batt_shown_scalars(summand: &Summand, gamma: &[E]) -> Vec<E> {
    let mut a = (summand.at)(gamma, &[]);
    a.remove(0);
    a
}

/// PSC's mask entries (`batt_shown_slots`, batt_shown.h:112-116).
pub fn batt_shown_slots(k_col: u32, own: &mut MaskLedger, index_masks: &mut MaskLedger) -> Vec<MaskSlot> {
    let mut fresh = own.take_n(batt_shown_own_masks(k_col));
    fresh.push(index_masks.take());
    fresh
}

/// The output claims (`batt_shown_rows`, batt_shown.h:117-129).
pub fn batt_shown_rows(rows: &[TensorRow], summand: &Summand, out: PscOutput) -> BattShown {
    assert!(
        out.ends.len() == 1 && out.row_maps.is_empty(),
        "BATT, shown: one end value and no kept map"
    );
    let a = batt_shown_scalars(summand, &out.point);
    let mut r = BattShown::default();
    for j in 0..rows.len() {
        for g in &rows[j].g {
            let mut g = g.clone();
            g.scalar = g.scalar * a[j];
            r.row.g.push(g);
        }
    }
    let end = out.ends.into_iter().next().unwrap();
    r.row.psi = end.point;
    r.row.masks = end.masks;
    r.row.target = end.value;
    r.own_masks = out.row_masks;
    r.own_target = out.row_target;
    r
}

/// The verifier's BATT-shown (`batt_shown_verify`, batt_shown.h:179-186).
pub fn batt_shown_verify(
    ch: &mut VerifierRounds<'_, '_, '_>,
    mut rows: Vec<TensorRow>,
    own: &mut MaskLedger,
    index_masks: &mut MaskLedger,
    calls: &mut HashCalls,
) -> (BattShown, bool) {
    let k_col = batt_k_col(&rows);
    let n = rows.len();
    let x = batt_draw(ch, n, calls);
    let b = batt_claim(&mut rows, x);
    let BattClaim { claim, summand, .. } = b;
    let mut o = PscOutput {
        point: Vec::new(),
        row_masks: Vec::new(),
        row_maps: Vec::new(),
        row_target: E::zero(),
        ends: Vec::new(),
    };
    if !psc_verify(
        ch,
        claim,
        &batt_shown_summand(),
        batt_shown_slots(k_col, own, index_masks),
        &mut o,
        calls,
    ) {
        return (BattShown::default(), false);
    }
    let out = batt_shown_rows(&rows, &summand, o);
    let ok = ch.ok();
    (out, ok)
}
