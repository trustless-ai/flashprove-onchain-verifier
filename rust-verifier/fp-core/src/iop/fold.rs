//! FOLD, ported from the verifier's side of `blocks/iop/fold.h` (lines 40-250, 256-282, 443-492).
//! The prover's engine, coins and self-checks are not ported; the verifier's checks and output
//! claim are.

use alloc::vec::Vec;

use super::context::{receive_oracles, VerifierContext};
use super::fold_algebra::{fold_mask_columns, fold_mask_weights};
use super::fold_rounds::{fold_mask_form, fold_kept_factor, FoldVerifierRounds};
use super::relation::{
    CodeId, GroupLayout, GroupRow, OracleId, OracleShape, Statement, NONE_ID,
};
use super::single_rows::{group_as_run, SingleRows};
use crate::chain::rounds::VerifierRounds;
use crate::code::code::mask_fits;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::PricedGroup;
use crate::numbers::round_names::{R_FOLD_EPSILON, R_FOLD_ROUND};

/// The public parameters of one FOLD (`FoldShape`, fold.h:40-64). The three prover-only options
/// stay for their public meaning and are ignored by the verifier's path.
#[derive(Clone, Debug)]
pub struct FoldShape {
    pub code: CodeId,
    pub mask_code: CodeId,
    pub layout: GroupLayout,
    pub mask_leaf_class: u32,
    pub keep_folded_coefficients: bool,
    pub folded_coefficients_alone: bool,
    pub target_from_the_rounds: bool,
}

impl Default for FoldShape {
    /// The C++ defaults are NONE_ID for both code numbers (fold.h:40-42).
    fn default() -> Self {
        FoldShape {
            code: NONE_ID,
            mask_code: NONE_ID,
            layout: GroupLayout::default(),
            mask_leaf_class: 0,
            keep_folded_coefficients: false,
            folded_coefficients_alone: false,
            target_from_the_rounds: false,
        }
    }
}

/// The fresh mask of one FOLD (`FoldMask`, fold.h:129-149). On the verifier's side only the id
/// matters; `w` is empty unless a prover-side caller sets it.
#[derive(Debug)]
pub struct FoldMask {
    w: Vec<E>,
    id: OracleId,
}

impl Default for FoldMask {
    fn default() -> Self {
        // `FoldMask`'s C++ default is id NONE_ID (fold.h:131); Rust's derive would say 0.
        FoldMask { w: Vec::new(), id: NONE_ID }
    }
}

impl FoldMask {
    pub fn sent(&self) -> bool {
        self.id != NONE_ID
    }
    pub fn id(&self) -> OracleId {
        self.id
    }
    pub fn sent_as(&mut self, id: OracleId) {
        assert!(!self.sent(), "FOLD: a fresh mask was told its number twice");
        self.id = id;
    }
    pub fn coefficients(&self) -> &[E] {
        &self.w
    }
    pub fn with_coefficients(w: Vec<E>) -> Self {
        FoldMask { w, id: NONE_ID }
    }
}

/// `fold_shape_check` (fold.h:77-99).
pub fn fold_shape_check(st: &Statement, S: &FoldShape) {
    let codes = st.codes();
    let L = &S.layout;
    assert!(
        (S.code as usize) < codes.base.len() && (S.mask_code as usize) < codes.mask.len(),
        "FOLD: the shape names a code that does not exist"
    );
    assert!(L.k >= 1 && L.h <= L.k, "FOLD: no row variable, or more mask rows than main rows");
    assert!(
        mask_fits(&codes.base[S.code as usize], &codes.mask[S.mask_code as usize]),
        "FOLD: the mask code is longer than the main code"
    );
    assert!(
        codes.mask[S.mask_code as usize].ell >= fold_mask_columns(L.k, L.h) as usize,
        "FOLD: the mask rows are too short for the hiding polynomial"
    );
    assert!(
        L.kept.len() == L.members.len()
            && L.main_first.len() == L.members.len()
            && L.mask_first.len() == L.members.len(),
        "FOLD: the layout's lists do not have one entry for each member"
    );
    let mut folds_something = false;
    for i in 0..L.members.len() {
        let o = &st.oracle(L.members[i]).shape;
        let folded = o.main_rows > 0 && !L.kept[i];
        folds_something = folds_something || folded;
        assert!(
            o.main_rows == 0 || o.code == S.code,
            "FOLD: a member's main rows are under another code than the group's"
        );
        assert!(
            o.mask_rows == 0 || o.mask_code == S.mask_code,
            "FOLD: a member's mask rows are under another code than the group's"
        );
        assert!(
            if folded {
                L.main_first[i] + o.main_rows as u64 <= 1u64 << L.k
            } else {
                L.main_first[i] == GroupLayout::NONE
            },
            "FOLD: a member's main rows do not lie among the group's 2^k rows, or rows that are not folded have a place there"
        );
        assert!(
            if o.mask_rows > 0 {
                L.mask_first[i] + o.mask_rows as u64 <= 1u64 << L.h
            } else {
                L.mask_first[i] == GroupLayout::NONE
            },
            "FOLD: a member's mask rows do not lie among the group's 2^h rows, or a member without mask rows has a place there"
        );
    }
    assert!(folds_something, "FOLD: no member of the group has a main row to fold");
}

/// `fold_row_check` (fold.h:101-109).
pub fn fold_row_check(st: &Statement, S: &FoldShape, row: &GroupRow) {
    let codes = st.codes();
    assert!(
        row.c.fits(S.layout.k + ceil_log2(codes.base[S.code as usize].ell as u64)),
        "FOLD: the claim's coefficients on the main rows have not the main table's length"
    );
    assert!(
        row.d.len() == codes.mask[S.mask_code as usize].ell << S.layout.h,
        "FOLD: the claim's coefficients on the mask rows have not the mask table's length"
    );
    for f in &row.kept {
        assert!(
            S.layout.kept[S.layout.find(f.oracle)],
            "FOLD: the claim has separate coefficients on a member that is not kept"
        );
        assert!(
            f.c.fits(st.table_bits(f.oracle, super::relation::Part::Main)),
            "FOLD: the claim's coefficients on a kept member have not its table's length"
        );
    }
}

/// `fold_mask_notice` (fold.h:177-185).
pub fn fold_mask_notice(S: &FoldShape) -> super::context::OracleNotice {
    super::context::OracleNotice {
        shape: OracleShape {
            name: alloc::string::String::from("fold mask"),
            code: NONE_ID,
            main_rows: 0,
            main_deg: 1,
            mask_rows: 1usize << S.layout.h,
            mask_code: S.mask_code,
            answers: 0,
        },
        leaf_class: S.mask_leaf_class,
    }
}

/// `fold_mask_check` (fold.h:198-204).
pub fn fold_mask_check(st: &Statement, S: &FoldShape, fresh: OracleId) {
    let o = st.oracle(fresh);
    assert!(
        o.shape.main_rows == 0
            && o.shape.mask_rows == 1usize << S.layout.h
            && o.shape.mask_code == S.mask_code,
        "FOLD: the oracle named as the fresh mask has not just 2^h mask rows under the group's mask code"
    );
    assert!(
        !o.sampled && o.shape.answers == 0,
        "FOLD: the oracle named as the fresh mask has an out-of-domain sample"
    );
    for m in &S.layout.members {
        assert!(*m != fresh, "FOLD: the oracle named as the fresh mask is a member of the group");
    }
}

/// FOLD after its first message (`FoldStart`, fold.h:206-240).
pub struct FoldStart {
    mask: FoldMask,
    sum: E,
    eps: E,
    has_eps: bool,
    code: CodeId,
    mask_code: CodeId,
    k: u32,
    h: u32,
    members: Vec<OracleId>,
    group: PricedGroup,
}

impl FoldStart {
    fn same_shape(&self, S: &FoldShape) {
        assert!(
            S.code == self.code
                && S.mask_code == self.mask_code
                && S.layout.k == self.k
                && S.layout.h == self.h
                && S.layout.members == self.members,
            "FOLD: the rounds are run for another shape than the first message"
        );
    }
    fn remember(st: &Statement, S: &FoldShape) -> Self {
        let mut kept_rows = 0u64;
        for i in 0..S.layout.members.len() {
            if S.layout.kept[i] {
                kept_rows += st.oracle(S.layout.members[i]).shape.main_rows as u64;
            }
        }
        FoldStart {
            mask: FoldMask::default(),
            sum: E::zero(),
            eps: E::zero(),
            has_eps: false,
            code: S.code,
            mask_code: S.mask_code,
            k: S.layout.k,
            h: S.layout.h,
            members: S.layout.members.clone(),
            group: group_as_run(
                st.codes(),
                S.code,
                S.mask_code,
                true,
                S.layout.k,
                S.layout.h,
                1u64 << ceil_log2(1 + kept_rows),
            ),
        }
    }
    pub fn eps(&self) -> E {
        self.eps
    }
}

/// Draws eps, the only element of its verifier message (`fold_epsilon`, fold.h:248-254).
pub fn fold_epsilon(ch: &mut VerifierRounds<'_, '_, '_>, s: &mut FoldStart, calls: &mut HashCalls) {
    assert!(!s.has_eps, "FOLD: eps was drawn twice");
    s.eps = ch.close_epsilon(R_FOLD_EPSILON, calls);
    ch.require_group(&s.group);
    s.has_eps = true;
}

/// FOLD's output; both sides compute it (`fold_output`, fold.h:261-282).
pub fn fold_output(
    st: &Statement,
    S: &FoldShape,
    mut row: GroupRow,
    fresh: OracleId,
    eps: E,
    gamma: &[E],
    claim: E,
) -> SingleRows {
    let codes = st.codes();
    let k = S.layout.k;
    let h = S.layout.h;
    let mut out = SingleRows {
        code: S.code,
        mask_code: S.mask_code,
        layout: S.layout.clone(),
        gamma: gamma.to_vec(),
        masks: 2,
        fresh,
        ..SingleRows::default()
    };
    out.c = core::mem::take(&mut row.c);
    out.c.fix_low(gamma, k, eps);
    out.kept = core::mem::take(&mut row.kept);
    for f in &mut out.kept {
        f.c.scale(fold_kept_factor(eps, gamma));
    }
    for i in 0..S.layout.members.len() {
        if S.layout.kept[i] {
            out.kept_rows += st.oracle(S.layout.members[i]).shape.main_rows;
        }
    }
    out.d.push(fold_mask_form(k, h, row.d, eps, gamma));
    out.d.push(fold_mask_weights(k, h, codes.mask[S.mask_code as usize].ell, gamma));
    out.target = claim;
    out
}

/// The verifier's first FOLD message (`fold_start_verify`, fold.h:444-457).
pub fn fold_start_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &FoldShape,
    mut mask: FoldMask,
    start: &mut Option<FoldStart>,
    _calls: &mut HashCalls,
) -> bool {
    fold_shape_check(&V.st, S);
    if !mask.sent() {
        let mut ids = Vec::new();
        if !receive_oracles(V, &[fold_mask_notice(S)], &mut ids) {
            return false;
        }
        mask.sent_as(ids[0]);
    }
    fold_mask_check(&V.st, S, mask.id());
    V.st.spend_as_mask(mask.id());
    let mut st = FoldStart::remember(&V.st, S);
    st.mask = mask;
    let ok = V.ch.recv_hiding_sum(&mut st.sum);
    *start = Some(st);
    ok
}

/// The verifier's FOLD rounds (`fold_rounds_verify`, fold.h:462-481).
pub fn fold_rounds_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &FoldShape,
    row: GroupRow,
    start: FoldStart,
    out: &mut SingleRows,
    calls: &mut HashCalls,
) -> bool {
    assert!(start.has_eps, "FOLD: eps has not been drawn");
    start.same_shape(S);
    fold_row_check(&V.st, S, &row);
    let mut claim = FoldVerifierRounds::new(start.sum, start.eps, row.target);
    let mut gamma = Vec::new();
    for _ in 0..S.layout.k {
        let mut c0 = E::zero();
        let mut c2 = E::zero();
        if !V.ch.recv_e(&mut c0) || !V.ch.recv_e(&mut c2) {
            return false;
        }
        let g = {
            let mut draw = V.ch.close_algebraic(R_FOLD_ROUND, calls);
            draw.draw(calls)
        };
        V.ch.require_group(&start.group);
        claim.round(c0, c2, g);
        gamma.push(g);
    }
    *out = fold_output(&V.st, S, row, start.mask.id(), start.eps, &gamma, *claim.claim());
    out.c.freeze(ceil_log2(V.st.codes().base[S.code as usize].ell as u64));
    V.ch.ok()
}

/// All of FOLD, the verifier's side (`fold_verify`, fold.h:487-492).
pub fn fold_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &FoldShape,
    row: GroupRow,
    mask: FoldMask,
    out: &mut SingleRows,
    calls: &mut HashCalls,
) -> bool {
    let mut start: Option<FoldStart> = None;
    if !fold_start_verify(V, S, mask, &mut start, calls) {
        return false;
    }
    fold_epsilon(V.ch, start.as_mut().unwrap(), calls);
    fold_rounds_verify(V, S, row, start.unwrap(), out, calls)
}
