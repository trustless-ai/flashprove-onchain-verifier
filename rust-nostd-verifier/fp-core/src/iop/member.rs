//! A request's own part of LIN, the verifier's side, ported from `blocks/iop/member.h`
//! (lines 40-186).
//!
//! A request's sub-proofs leave J >= 1 pending claims on the table's matrix M:
//! `< g (x) eq(psi, .), M > + (mask entries) = value`. `member_first_verify` batches them into one
//! with BATT if J > 1 and runs LIN's first part; the caller then seals the chain and runs LIN's
//! shared and second parts itself.
//!
//! Ported: `member_claim`, `member_inner::stretch_in_the_cube`, `member_weights_on_rows`,
//! `member_pending_row`, `member_rows_fit` and `member_first_verify`. Not ported, because only a
//! prover's engine and coins use them: `MemberHeavy`, `member_first_prove` and `plan_member_rows`.
//!
//! Deviations at the verifier's boundary: `member_first_verify` lends `HashCalls` explicitly; the
//! shared vector of stretched weights is the port's `Rc<Vec<E>>` where C++ keeps
//! `shared_ptr<const vector<E>>`.

use alloc::rc::Rc;
use alloc::vec::Vec;

use super::batt::{batt_k_col, batt_verify, TensorRow};
use super::context::VerifierContext;
use super::lin::{lin_first_verify, LinClaim, LinFirst, LinPublic, LinShape};
use super::mask::{MaskSlot, MaskTerm};
use super::relation::OracleId;
use super::tensor::Tensor;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;

/// A pending claim in LIN's form (`member_claim`, member.h:41-49). Consumes the claim's mask
/// entries.
pub fn member_claim(mut row: TensorRow) -> LinClaim {
    let mut c = LinClaim {
        g: core::mem::take(&mut row.g),
        psi: core::mem::take(&mut row.psi),
        masks: Vec::new(),
        target: row.target,
    };
    for m in row.masks.drain(..) {
        c.add_mask(m.slot, m.coeff);
    }
    c
}

/// Row weights given as a vector on a range of rows (`stretch_in_the_cube`, member.h:57-86).
/// `values[i]` lies on row `first_row + i`, and zero on the rest of the cube. The range is cut into
/// aligned blocks of 2^d rows, at most two of each size. A block of two or more rows is one
/// `Tensor` whose dense factor is a slice of the shared vector; a block of one row has its value
/// read here and stored as the Tensor's scalar.
pub mod member_inner {
    use super::*;

    pub fn stretch_in_the_cube(
        k_row: u32,
        first_row: u64,
        values: Rc<Vec<E>>,
    ) -> Vec<Tensor> {
        assert!(
            k_row < 63
                && first_row.wrapping_add(values.len() as u64) <= (1u64 << k_row),
            "member: the stretch of rows does not lie in the cube"
        );
        let mut g = Vec::new();
        let mut at = first_row;
        let end = first_row + values.len() as u64;
        while at < end {
            // The largest aligned block that begins at `at` and ends by `end`.
            let mut d = 0u32;
            while d < k_row
                && (at & ((2u64 << d) - 1)) == 0
                && at + (2u64 << d) <= end
            {
                d += 1;
            }
            let mut t = Tensor::default();
            if d == 0 {
                t.scalar = values[(at - first_row) as usize];
                t.insert_choice(0, k_row, at);
            } else {
                t.push_dense(d);
                t.insert_choice(d, k_row - d, at >> d);
                t.set_values(values.clone(), at - first_row);
            }
            g.push(t);
            at += 1u64 << d;
        }
        g
    }
}

/// `stretch_in_the_cube` for callers: ends the process unless the range is inside the matrix
/// (`member_weights_on_rows`, member.h:92-97). LIN silently ignores weights from row `matrix_rows`
/// on, so a caller whose layout has more rows than `LinShape` counts would lose its claims.
pub fn member_weights_on_rows(
    S: &LinShape,
    first_row: u64,
    values: Rc<Vec<E>>,
) -> Vec<Tensor> {
    assert!(
        first_row.wrapping_add(values.len() as u64) <= S.matrix_rows,
        "member: a stretch of row weights does not lie inside the matrix"
    );
    member_inner::stretch_in_the_cube(S.k_row(), first_row, values)
}

/// The pending claim that a sub-proof leaves (`member_pending_row`, member.h:102-109):
/// `< g (x) eq(psi, .), M > + beta c = v`. `c` is consumed.
pub fn member_pending_row(
    g: Vec<Tensor>,
    psi: Vec<E>,
    c: MaskSlot,
    beta: E,
    v: E,
) -> TensorRow {
    TensorRow {
        g,
        psi,
        masks: alloc::vec![MaskTerm { slot: c, coeff: beta }],
        target: v,
    }
}

/// Checks the pending claims and the index-mask message against `LinShape`
/// (`member_rows_fit`, member.h:137-150). Both sides run it first; a mismatch ends the process.
pub fn member_rows_fit(
    st: &super::relation::Statement,
    S: &LinShape,
    index_masks: OracleId,
    pending: &[TensorRow],
) {
    let o = &st.oracle(index_masks).shape;
    assert!(
        o.main_rows == 0
            && o.mask_rows > 0
            && o.answers > 0
            && o.mask_code == S.own_mask_code,
        "member: the index-mask message is no sampled message of mask rows alone under the own group's mask code"
    );
    for r in pending {
        for m in &r.masks {
            assert!(
                m.slot.oracle() == index_masks,
                "member: a pending row names a mask entry outside the index-mask message"
            );
        }
    }
    assert!(!pending.is_empty(), "member: no pending row");
    assert!(
        batt_k_col(pending) == S.k_col(),
        "member: the pending rows' points do not fit the matrix's columns"
    );
    for r in pending {
        for t in &r.g {
            assert!(
                t.vars() == S.k_row(),
                "member: a pending row's weights do not fit the matrix's rows"
            );
        }
    }
}

/// The verifier's side of the first part (`member_first_verify`, member.h:168-185). False if BATT
/// or LIN's first part rejects.
#[allow(clippy::too_many_arguments)]
pub fn member_first_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    x: &LinPublic,
    index_masks: OracleId,
    pending: Vec<TensorRow>,
    out: &mut LinFirst,
    calls: &mut HashCalls,
) -> bool {
    let S = V.ch.get(&x.shape).clone();
    member_rows_fit(&V.st, &S, index_masks, &pending);
    let one: TensorRow;
    if pending.len() > 1 {
        let (row, good) = {
            let masks = V.st.masks(index_masks);
            batt_verify(V.ch, pending, masks, calls)
        };
        if !good {
            return false;
        }
        one = row;
        if V.notes.is_some() {
            // To compare another verifier with this one block by block; changes nothing.
            V.note("BATT: target", one.target);
            V.note("BATT: gamma_0", one.psi[0]);
            V.note("BATT: the first weight's scalar", one.g[0].scalar);
            let c = one.masks.first().unwrap().coeff;
            V.note("BATT: coefficient of its first mask entry", c);
            let c = one.masks.last().unwrap().coeff;
            V.note("BATT: coefficient of the last mask term", c);
        }
    } else {
        one = pending.into_iter().next().unwrap();
    }
    V.note("member: the claim's target", one.target);
    lin_first_verify(V, x, member_claim(one), out, calls)
}

/// The pending claims on the table, as BATT if there are several (`plan_member_rows`,
/// member.h:116-118).
pub fn plan_member_rows(
    p: &mut crate::numbers::plan::Plan,
    where_: &str,
    rows: u64,
    k_col: u32,
) {
    if rows > 1 {
        crate::numbers::blocks::plan_batt(p, where_, rows, k_col);
    }
}
