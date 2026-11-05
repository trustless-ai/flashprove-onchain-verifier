//! The pending claim on the weight table, ported from `verifier/src/vf_weights_pending_claim.h`.

use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::iop::lin::LinShape;
use crate::iop::member::member_weights_on_rows;
use crate::iop::tensor::Tensor;
use crate::refusal::{Refusal, Result};

use super::weights_layout::{ws_gamma_add, WsForkOut, WsLay};

/// The claim without `c` (`struct WsPending`).
pub struct WsPending {
    /// The row weights are their sum.
    pub g: Vec<Tensor>,
    /// The point on the columns, the coordinate of column bit 0 first.
    pub psi: Vec<E>,
    pub beta: E,
    pub target: E,
}

/// `wsPending`.
pub fn ws_pending(lay: &WsLay, o: &WsForkOut, claims: usize, s: &LinShape) -> Result<WsPending> {
    let row_bits = s.k_row();
    if lay.m0 != s.matrix_rows {
        return Err(Refusal::named("internal-gamma-rows"));
    }
    if o.rec.is_empty() || o.rec.len() != claims || o.merged.rm.len() != lay.lk as usize {
        return Err(Refusal::named("link-claim-count"));
    }
    let mut first = u64::MAX;
    let mut last = 0u64;
    for c in &o.rec {
        if c.ui as usize >= lay.u.len() {
            return Err(Refusal::named("internal-gamma-rows"));
        }
        first = first.min(lay.u[c.ui as usize].off);
        last = last.max(lay.u[c.ui as usize].off + lay.u[c.ui as usize].rows);
    }
    if first >= last || last > lay.m0 || row_bits > 62 || lay.m0 > (1u64 << row_bits) {
        return Err(Refusal::named("internal-gamma-rows"));
    }
    let mut gam = vec![E::zero(); last as usize];
    for c in &o.rec {
        ws_gamma_add(&mut gam, lay, c, E::one())?;
    }
    let values: Vec<E> = gam[first as usize..last as usize].to_vec();
    let g = member_weights_on_rows(s, first, Rc::new(values));
    let mut psi = vec![E::zero(); o.merged.rm.len()];
    for i in 0..psi.len() {
        psi[i] = o.merged.rm[psi.len() - 1 - i];
    }
    Ok(WsPending { g, psi, beta: o.merged.beta, target: o.merged.fvp })
}
