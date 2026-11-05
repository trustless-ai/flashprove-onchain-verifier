//! The merge of a sub-proof's claims on the weight table, ported from
//! `verifier/src/vf_weights_merge.h`.
//!
//! One challenge's powers batch the claims, then a masked sumcheck over the table's `lk` column
//! bits fixes the columns at one point `rm`. The claim on the sub-proof's mask entries is left to
//! `wsForkLin`; the pending claim on the weight table is built by
//! [`super::weights_pending::ws_pending`].

use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::refusal::Result;

use super::engine::{Aff, HFork};
use super::sumcheck::{
    psc_begin, psc_ends, psc_row, round_in, sumcheck_slots, Psc, RoundForm,
};
use super::transcript::{tr_batch, Tr};

/// `struct WsMerged`.
pub struct WsMerged {
    /// `fv'`, as it was sent.
    pub fvp: E,
    /// The factor of its mask `c`.
    pub beta: E,
    /// The merge's point, the highest column bit first.
    pub rm: Vec<E>,
    pub p: Psc,
    /// The slot of `fv'`.
    pub s_fv: u32,
}

/// `wsForkMerge`: returns the merge's state and `rho[a]`.
pub fn ws_fork_merge(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    lk: i32,
    sv: &[u32],
    calls: &mut HashCalls,
) -> Result<(WsMerged, Vec<E>)> {
    let rho = tr_batch(tr, sv.len(), calls)?;
    let mut start = Aff::default();
    for a in 0..sv.len() {
        start.add(&Aff::slot(sv[a]), rho[a]);
    }
    let mut o = WsMerged {
        fvp: E::zero(),
        beta: E::zero(),
        rm: vec![E::zero(); lk as usize],
        p: psc_begin(f, tr, slot, &start, calls)?,
        s_fv: 0,
    };
    for i in 0..lk as usize {
        o.rm[i] = round_in(f, tr, slot, RoundForm::Sum2, &mut o.p, E::zero(), 0, calls)?;
    }
    o.s_fv = psc_ends(f, tr, slot, &mut o.p, 1, 1, calls)?;
    o.fvp = f.shown(o.s_fv)?;
    o.beta = *o.p.r.last().unwrap();
    Ok((o, rho))
}

/// `wsForkLin`: adds PSC's one remaining claim, the sub-proof's last.
pub fn ws_fork_lin(f: &mut HFork, o: &mut WsMerged) -> Result<()> {
    let row = psc_row(f, &mut o.p, o.fvp, &Aff::default())?;
    f.lin(&row)
}

/// `wsForkSlots(lk)`.
pub const fn ws_fork_slots(lk: i32) -> u64 {
    sumcheck_slots(RoundForm::Sum2, lk, 1, 1, 0)
}
