//! The transcript adapter of `verifier/src/vf_transcript_calls.h` and
//! `verifier/src/vf_transcript_channel.h`.
//!
//! C++ `Tr` (`vf_common.h:915-917`) is one reference to the chain's `VerifierRounds`; the `tr*`
//! functions are thin wrappers over `chain*`, which read and draw on the channel. This port keeps
//! the three lifetimes of `VerifierRounds` explicit and adds a borrow lifetime for `Tr`:
//! `Tr<'x, 'a, 'd, 's>` holds `&'x mut VerifierRounds<'a, 'd, 's>`.
//!
//! A failed read or draw is `chainHeld()` in C++: it prints `chain: <why>` and rejects under the
//! single name `chain-refused`. A `no_std` core cannot print, so every wrapper returns
//! `Err(Refusal::named("chain-refused"))` and the caller reads the reason through [`Tr::why`]
//! while the channel is still alive (the session keeps only the refusal flag). A fault of the
//! calling program is a panic in `VerifierRounds`; the two explicit C++ refusals
//! (`internal-batching-bare`, and by construction no `internal-round-name`) stay `Refusal`s.
//!
//! `trAnswer` and `trPoint` reject `BAT_SIGMA` before touching the channel; only `trBatch` and
//! `trBatchOpen` draw that round, because the channel must also be given the number of claims.
//! `trTrits` requires the planned number of combinations *before* an entry is drawn, as C++ does;
//! that is why [`crate::chain::rounds::BitsDraw::require_combinations`] exists.

use alloc::vec::Vec;

use crate::chain::rounds::VerifierRounds;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::round_names::{
    R_BAT_SIGMA, R_FOREST_POINT, R_JOIN, R_LINE, R_LKP, R_LKP_PLANES, R_LKP_SHIFT, R_PSC_EPSILON,
    R_PSC_ROUND, R_PSC_VALUES, R_PSC_Y, R_RNG, R_ZERO,
};
use crate::refusal::{Refusal, Result};

/// `enum class RoundName` (`vf_transcript_calls.h:30`): the kind of a call's round, not its place.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RoundName {
    PscEpsilon,
    PscRound,
    PscY,
    Line,
    Zero,
    BatSigma,
    Lkp,
    LkpShift,
    LkpPlanes,
    ForestPoint,
    Join,
    PscValues,
}

/// `roundName()` (`vf_transcript_channel.h:24-40`). The C++ fallthrough `internal-round-name` is
/// unreachable here: this match is exhaustive. `LkpPlanes`, `ForestPoint` and `Join` share
/// `"JOIN"`, as the chain's names do.
pub const fn round_name(r: RoundName) -> &'static str {
    match r {
        RoundName::PscEpsilon => R_PSC_EPSILON,
        RoundName::PscRound => R_PSC_ROUND,
        RoundName::PscY => R_PSC_Y,
        RoundName::Line => R_LINE,
        RoundName::Zero => R_ZERO,
        RoundName::BatSigma => R_BAT_SIGMA,
        RoundName::Lkp => R_LKP,
        RoundName::LkpShift => R_LKP_SHIFT,
        RoundName::LkpPlanes => R_LKP_PLANES,
        RoundName::ForestPoint => R_FOREST_POINT,
        RoundName::Join => R_JOIN,
        RoundName::PscValues => R_PSC_VALUES,
    }
}

/// The sub-proofs' handle on the channel (`struct Tr`, `vf_common.h:915-917`). Hash counters are
/// passed separately to the wrappers that need them, as everywhere else in the port.
pub struct Tr<'x, 'a, 'd, 's> {
    pub one: &'x mut VerifierRounds<'a, 'd, 's>,
}

impl<'x, 'a, 'd, 's> Tr<'x, 'a, 'd, 's> {
    pub fn new(one: &'x mut VerifierRounds<'a, 'd, 's>) -> Self {
        Self { one }
    }

    /// The channel's verdict so far.
    pub fn ok(&self) -> bool {
        self.one.ok()
    }

    /// The first reason for a rejection, to print as C++ `chainHeld()` prints `chain: <why>`
    /// before `NO: chain-refused`. The text is static and survives the channel.
    pub fn why(&self) -> Option<&'static str> {
        self.one.why()
    }
}

/// The C++ `chainHeld()`'s refusal. The caller prints `Tr::why()` first.
fn chain_refused() -> Refusal {
    Refusal::named("chain-refused")
}

fn chain_held(tr: &Tr<'_, '_, '_, '_>) -> Result<()> {
    if tr.one.ok() {
        Ok(())
    } else {
        Err(chain_refused())
    }
}

/// `chainNoBatching` (`vf_transcript_channel.h:75-77`).
fn chain_no_batching(round: RoundName) -> Result<()> {
    if round == RoundName::BatSigma {
        Err(Refusal::internal("internal-batching-bare"))
    } else {
        Ok(())
    }
}

/// `trRead` (`vf_transcript_calls.h:33`): `n` field elements of the prover's message.
pub fn tr_read(tr: &mut Tr<'_, '_, '_, '_>, n: usize) -> Result<Vec<E>> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let mut x = E::default();
        if !tr.one.recv_e(&mut x) {
            return Err(chain_refused());
        }
        v.push(x);
    }
    Ok(v)
}

/// `trSum` (`vf_transcript_calls.h:34`): a hiding polynomial's sum, which must be the last value
/// before `PSC_EPSILON`.
pub fn tr_sum(tr: &mut Tr<'_, '_, '_, '_>) -> Result<E> {
    let mut y = E::default();
    if !tr.one.recv_hiding_sum(&mut y) {
        return Err(chain_refused());
    }
    Ok(y)
}

/// `trAnswer` (`vf_transcript_calls.h:35`): one challenge.
pub fn tr_answer(
    tr: &mut Tr<'_, '_, '_, '_>,
    round: RoundName,
    calls: &mut HashCalls,
) -> Result<E> {
    chain_no_batching(round)?;
    let y = if round == RoundName::PscEpsilon {
        tr.one.close_epsilon(round_name(round), calls)
    } else {
        tr.one.close_algebraic(round_name(round), calls).draw(calls)
    };
    chain_held(tr)?;
    Ok(y)
}

/// `trAnswerNotZero` (`vf_transcript_calls.h:36`): one challenge, never 0.
pub fn tr_answer_not_zero(
    tr: &mut Tr<'_, '_, '_, '_>,
    round: RoundName,
    calls: &mut HashCalls,
) -> Result<E> {
    chain_no_batching(round)?;
    let y = tr.one.close_algebraic(round_name(round), calls).draw_nonzero(calls);
    chain_held(tr)?;
    Ok(y)
}

/// `trTrits` (`vf_transcript_calls.h:39`): the matrix of the approximate range check, column by
/// column, `combinations` entries each.
pub fn tr_trits(
    tr: &mut Tr<'_, '_, '_, '_>,
    columns: usize,
    combinations: usize,
    calls: &mut HashCalls,
) -> Result<Vec<i8>> {
    let v = {
        let mut from = tr.one.close_bits(R_RNG, calls);
        // Before an entry is drawn, as C++ `chainTrits` does.
        from.require_combinations(combinations as u64);
        from.trits(columns.wrapping_mul(combinations), calls)
    };
    chain_held(tr)?;
    Ok(v)
}

/// `trEmpty` (`vf_transcript_calls.h:41`): a round in which the verifier says nothing.
pub fn tr_empty(
    tr: &mut Tr<'_, '_, '_, '_>,
    round: RoundName,
    calls: &mut HashCalls,
) -> Result<()> {
    tr.one.close_empty(round_name(round), calls);
    chain_held(tr)
}

/// `trPoint` (`vf_transcript_calls.h:42`): `n` challenges of one round.
pub fn tr_point(
    tr: &mut Tr<'_, '_, '_, '_>,
    round: RoundName,
    n: usize,
    calls: &mut HashCalls,
) -> Result<Vec<E>> {
    chain_no_batching(round)?;
    let v = {
        let mut draw = tr.one.close_algebraic(round_name(round), calls);
        let mut v = Vec::with_capacity(n);
        // C++ draws all n even after a fault, then holds the chain.
        for _ in 0..n {
            v.push(draw.draw(calls));
        }
        v
    };
    chain_held(tr)?;
    Ok(v)
}

/// `trBatch` (`vf_transcript_calls.h:44`): one element `x` drawn for `rows` claims; returns
/// `x^0 .. x^(rows - 1)`.
pub fn tr_batch(
    tr: &mut Tr<'_, '_, '_, '_>,
    rows: usize,
    calls: &mut HashCalls,
) -> Result<Vec<E>> {
    if rows == 0 {
        return Err(Refusal::internal("internal-batching-bare"));
    }
    let x = {
        let mut from = tr.one.close_algebraic(R_BAT_SIGMA, calls);
        from.require_rows(rows as u64);
        from.draw(calls)
    };
    chain_held(tr)?;
    let mut v = Vec::with_capacity(rows);
    let mut last = E::one();
    v.push(last);
    for _ in 1..rows {
        last *= x;
        v.push(last);
    }
    Ok(v)
}

/// `trBatchOpen` (`vf_transcript_calls.h:45`): the same round for a caller that counts its claims
/// after the draw; returns `x`, and [`tr_batch_rows`] must follow.
pub fn tr_batch_open(tr: &mut Tr<'_, '_, '_, '_>, calls: &mut HashCalls) -> Result<E> {
    let y = tr.one.close_algebraic(R_BAT_SIGMA, calls).draw(calls);
    chain_held(tr)?;
    Ok(y)
}

/// `trBatchRows` (`vf_transcript_calls.h:49`): the number of claims that the last draw batched.
pub fn tr_batch_rows(tr: &mut Tr<'_, '_, '_, '_>, rows: u64) {
    tr.one.require_rows(rows);
}
