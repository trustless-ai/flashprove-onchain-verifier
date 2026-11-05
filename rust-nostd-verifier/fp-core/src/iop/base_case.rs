//! BASE, the last step of a proximity test, ported from the verifier's side of
//! `blocks/iop/base_case.h` (lines 50-119, 196-247). The prover's engine and draw checks are not
//! ported.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use super::context::{receive_oracles, read_opened, OracleNotice, VerifierContext};
use super::fold_algebra::inner;
use super::relation::{CodeId, OracleId, OracleShape, NONE_ID};
use super::send_pad::send_pad_len;
use super::single_rows::{
    group_as_run, single_rows_main_form, single_rows_oracles, single_rows_symbols, SingleRows,
};
use crate::code::code::{mask_fits, mask_position, symbol_at, Code};
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::round_names::{R_BASE, R_BASE_LAMBDA};

/// One BASE's masking oracle (`BaseMask`, base_case.h:50-74). The verifier sets only `id`.
#[derive(Debug)]
pub struct BaseMask {
    id: OracleId,
}

impl Default for BaseMask {
    /// The C++ default is NONE_ID (base_case.h:73).
    fn default() -> Self {
        BaseMask { id: NONE_ID }
    }
}

impl BaseMask {
    pub fn sent(&self) -> bool {
        self.id != NONE_ID
    }
    pub fn id(&self) -> OracleId {
        self.id
    }
    pub fn sent_as(&mut self, id: OracleId) {
        assert!(!self.sent(), "BASE: a masking oracle was told its number twice");
        self.id = id;
    }
    pub fn new() -> Self {
        BaseMask { id: NONE_ID }
    }
}

/// `base_mask_notice` (base_case.h:91-99).
pub fn base_mask_notice(code: CodeId, mask_code: CodeId, masks: u32, leaf_class: u32) -> OracleNotice {
    OracleNotice {
        shape: OracleShape {
            name: String::from("base mask"),
            code,
            main_rows: 1,
            main_deg: 3,
            mask_code,
            mask_rows: masks as usize,
            answers: 0,
        },
        leaf_class,
    }
}

/// `base_shape_check` (base_case.h:110-119).
pub fn base_shape_check(st: &super::relation::Statement, S: &SingleRows, star: OracleId) {
    let o = st.oracle(star);
    assert!(
        S.kept_rows == 0 && S.kept.is_empty(),
        "BASE: the complex has kept rows"
    );
    assert!(
        S.masks == 0
            || mask_fits(&st.codes().base[S.code as usize], &st.codes().mask[S.mask_code as usize]),
        "BASE: the mask code is longer than the main code"
    );
    assert!(
        o.shape.main_rows == 1
            && o.shape.main_deg == 3
            && o.shape.code == S.code
            && o.shape.mask_rows == S.masks as usize
            && (S.masks == 0 || o.shape.mask_code == S.mask_code),
        "BASE: the oracle named as the masking oracle has not one row for each row of the complex, under the same codes"
    );
    assert!(
        !o.sampled && o.shape.answers == 0,
        "BASE: the oracle named as the masking oracle has an out-of-domain sample"
    );
    for m in single_rows_oracles(S) {
        assert!(m != star, "BASE: the oracle named as the masking oracle is one of the oracles that it is to mask");
    }
}

/// The verifier's BASE (`base_verify`, base_case.h:196-247).
pub fn base_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &SingleRows,
    mut mask: BaseMask,
    leaf_class: u32,
    calls: &mut HashCalls,
) -> bool {
    let code = V.st.codes().base[S.code as usize].clone();
    if !mask.sent() {
        let mut got = Vec::new();
        if !receive_oracles(V, &[base_mask_notice(S.code, S.mask_code, S.masks, leaf_class)], &mut got) {
            return false;
        }
        mask.sent_as(got[0]);
    }
    base_shape_check(&V.st, S, mask.id());
    V.st.spend_as_mask(mask.id());
    let mut target_star = E::zero();
    if !V.ch.recv_e(&mut target_star) {
        return false;
    }
    let lambda = {
        let mut draw = V.ch.close_algebraic(R_BASE_LAMBDA, calls);
        draw.draw(calls)
    };
    V.ch.require_group(&group_as_run(
        V.st.codes(),
        S.code,
        S.mask_code,
        S.masks != 0,
        0,
        0,
        1,
    ));

    let rows = S.rows();
    let mut m: Vec<Vec<E>> = Vec::with_capacity(rows);
    let mut r: Vec<Vec<E>> = Vec::with_capacity(rows);
    for j in 0..rows {
        let cj: &Code = if j == 0 {
            &code
        } else {
            &V.st.codes().mask[S.mask_code as usize]
        };
        m.push(vec![E::zero(); cj.ell]);
        r.push(vec![E::zero(); cj.r]);
    }
    for row in &mut m {
        for x in row.iter_mut() {
            if !V.ch.recv_e(x) {
                return false;
            }
        }
    }
    for row in &mut r {
        for x in row.iter_mut() {
            if !V.ch.recv_e(x) {
                return false;
            }
        }
    }
    let mut left = inner(&single_rows_main_form(S, code.ell), &m[0]);
    for j in 0..S.masks as usize {
        left = left + inner(&S.d[j], &m[1 + j]);
    }
    if V.notes.is_some() {
        V.note("BASE: left side of the linear check", left);
        V.note("BASE: right side of the linear check", target_star + lambda * S.target);
    }
    if left != target_star + lambda * S.target {
        V.ch.refuse("BASE: the masked message in the proof does not satisfy the linear claim");
        return false;
    }

    let at = {
        let mut draw = V.ch.close_positions(R_BASE, calls);
        draw.positions(code.log_n, calls)
    };
    V.ch.require_codes(&group_as_run(
        V.st.codes(),
        S.code,
        S.mask_code,
        S.masks != 0,
        0,
        0,
        1,
    ));
    if !V.ch.ok() {
        return false;
    }

    let mut ids = single_rows_oracles(S);
    ids.push(mask.id());
    let mut opened = super::context::Opened::default();
    if !read_opened(V, &ids, &at, &mut opened, calls) {
        return false;
    }
    let y = single_rows_symbols(S, &opened, at.size());
    for i in 0..at.size() {
        let star = &opened.of.last().unwrap()[i];
        for j in 0..rows {
            let cj: &Code = if j == 0 {
                &code
            } else {
                &V.st.codes().mask[S.mask_code as usize]
            };
            let x = if j == 0 { at.at(i) } else { mask_position(&code, cj, at.at(i)) };
            let masked = (if j == 0 { star.main[0] } else { star.mask[j - 1] })
                + lambda * y[i * S.rows() + j];
            if symbol_at(cj, x, &m[j], &r[j]) != masked {
                V.ch.refuse("BASE: the encoding of the masked message differs from the opened symbols at a listed position");
                return false;
            }
        }
    }
    true
}

/// The pad length of a message (`Send::pad(...).size()`, used by CS and callers).
pub fn pad_len(codes: &super::relation::Codes, s: &OracleShape) -> usize {
    send_pad_len(codes, s)
}
