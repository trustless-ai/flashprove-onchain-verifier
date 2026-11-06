//! LIN, ported from the verifier's side of `blocks/iop/lin.h`.
//!
//! LIN proves one linear claim for each request of a batch on one committed table (`Index`), with
//! one fold of the table for the whole batch, and leaves no linear claim open: it ends in
//! proximity tests. The table stores a matrix M (`LinShape`). Request c claims, for public g_c,
//! psi_c, tau_c (`LinClaim`):
//!     < g_c (x) eq(psi_c, .), M >  +  (mask entries of its own oracle messages)  =  tau_c.
//!
//! LIN has three parts, each on its own hash chain: first, each request sends W_c = g_c^T M;
//! shared, once a batch, the verifier draws psi*, the prover sends G_u (the table's rows folded
//! into one) and Omega = M eq(psi*, .); second, each request ties < g_c, Omega > to W_c at psi*.
//!
//! Ported: the shapes and their faults, the three messages' oracle notices, `LinPublic` and the
//! binding functions, the claims (`LinClaim`, `lin_eval_row`, `lin_fold_row`, `lin_dot_row`), the
//! first, shared and second verifier parts with their tests, the binding tree's shape, hashes,
//! root reading and the hash-chain binder functions.
//!
//! Not ported, because they are the prover's or use the engine and coins: `LinBinding` (the tree
//! builder), `LinBegun`/`lin_begin`, every `*_prove*` entry point, `lin_weights_of_the_prover`,
//! `lin_table`, `lin_draft`, `lin_masks_as_drawn`, `lin_release`, and `lin_go_on` (the port's
//! `VerifierContext::goes_on` already does the verifier's move). The two chain labels
//! `LIN_LABEL_SHARED`/`LIN_LABEL_SECOND` are key-file numbers; no verifier function in this file
//! reads them, so they are left to the frame layer.
//!
//! `lin_draw` is the verifier side of the C++ template over `Channel`: it closes the round and
//! draws the same number of elements of E. `std::move` of a claim is Rust's by-value `claim`.
//! Hash calls are explicit, as everywhere else in the port.

use alloc::vec::Vec;

use super::context::{OracleNotice, TreeBook, VerifierContext};
use super::foldeq::{
    foldeq_fault, foldeq_verify, priced_table, tensor_below, vector_lay, vector_room, FoldedRow,
    FoldeqShape, IndexName, TableRead, VectorLay,
};
use super::fold::{fold_mask_notice, FoldMask, FoldShape};
use super::iopp::{iopp_fold_shape, iopp_verify, IoppChoice, IoppStage};
use super::message::{Reader, Writer};
use super::relation::{
    Codes, CodeId, GroupId, GroupLayout, OracleId, OracleShape, Part, Row, Statement, Unit,
    NONE_ID,
};
use super::send::{send_verify, AnswersRound};
use super::split::split_verify;
use super::tensor::Tensor;
use crate::chain::public::{Binder, Public, PublicBytes, Sealed};
use crate::chain::rounds::VerifierRounds;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::hash::domains::Domain;
use crate::hash::modes::{leaf_digest, salt_length_fits, vertex, Digest, Tag};
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::TableTest;
use crate::numbers::round_names::{R_LIN_POINT, R_LIN_ZETA};
use crate::tree::tree::tree_index;

/// The two chain labels, ASCII "LIN" then 1 or 2 (`LIN_LABEL_SHARED`, `LIN_LABEL_SECOND`,
/// lin.h:54). Kept for the frame layer; no function below reads them.
pub const LIN_LABEL_SHARED: u64 = 0x4c494e01;
pub const LIN_LABEL_SECOND: u64 = 0x4c494e02;

// ------------------------------------------------------------------------------------------------
// The public shape
// ------------------------------------------------------------------------------------------------

/// The matrix and the oracle messages of the test (`LinShape`, lin.h:68-96).
///
/// M has `matrix_rows` rows and `2^k_col()` columns: a row's index has `k_row()` bits, a column's
/// `k_col()`. Entry (y, j + 2^k_lo r) of M, j < 2^k_lo, is message entry j + 2^k_lo y of row r of
/// the table, which has 2^v rows (`fold.index.v`).
#[derive(Clone, Debug)]
pub struct LinShape {
    pub fold: FoldeqShape,
    pub k_lo: u32,
    pub matrix_rows: u64,
    pub omega: OracleShape,
    pub w: OracleShape,
    pub omega_rows_high: bool,
    pub w_rows_high: bool,
    pub shared_split: OracleShape,
    pub own_split: OracleShape,
    pub omega_leaf_class: u32,
    pub shared_split_leaf_class: u32,
    pub w_leaf_class: u32,
    pub own_split_leaf_class: u32,
    pub shared_mask_code: CodeId,
    pub own_mask_code: CodeId,
    pub masks_ahead: bool,
    pub test_u: Vec<IoppStage>,
    pub test_omega: Vec<IoppStage>,
    pub test_own: Vec<IoppStage>,
    pub test_own_omega: Vec<IoppStage>,
    pub choice: IoppChoice,
}

impl Default for LinShape {
    /// The C++ member defaults (lin.h:68-96).
    fn default() -> Self {
        LinShape {
            fold: FoldeqShape::default(),
            k_lo: 0,
            matrix_rows: 0,
            omega: OracleShape::default(),
            w: OracleShape::default(),
            omega_rows_high: false,
            w_rows_high: false,
            shared_split: OracleShape::default(),
            own_split: OracleShape::default(),
            omega_leaf_class: 1,
            shared_split_leaf_class: 2,
            w_leaf_class: 0,
            own_split_leaf_class: 3,
            shared_mask_code: 0,
            own_mask_code: 0,
            masks_ahead: false,
            test_u: Vec::new(),
            test_omega: Vec::new(),
            test_own: Vec::new(),
            test_own_omega: Vec::new(),
            choice: IoppChoice::default(),
        }
    }
}

impl LinShape {
    /// `k_col()` (lin.h:92).
    pub fn k_col(&self) -> u32 {
        self.k_lo + self.fold.index.v
    }
    /// `k_row()` (lin.h:93).
    pub fn k_row(&self) -> u32 {
        ceil_log2(self.matrix_rows)
    }
    /// `shared_split_needed()` (lin.h:94).
    pub fn shared_split_needed(&self) -> bool {
        self.fold.u.code != self.omega.code
    }
    /// `own_split_needed()` (lin.h:95).
    pub fn own_split_needed(&self) -> bool {
        self.w.code != self.omega.code
    }
}

/// Null, or what is wrong with the shape by itself (`public_fault(const LinShape&)`, lin.h:99-120).
pub fn lin_public_fault(S: &LinShape) -> Option<&'static str> {
    if let Some(f) = S.fold.public_fault() {
        return Some(f);
    }
    if S.matrix_rows < 1 || S.k_lo > 30 || S.k_row() > 30 || S.k_col() > 60 {
        return Some("the matrix has no rows, or too many rows or columns");
    }
    if (S.matrix_rows << S.k_lo) > S.fold.index.plain() as u64 {
        return Some("the matrix does not fit the table's rows beside their pads");
    }
    for o in [&S.omega, &S.w] {
        if let Some(f) = o.public_fault() {
            return Some(f);
        }
        if o.main_rows == 0 || o.main_deg != super::foldeq::E_DEGREE as u32 {
            return Some("an oracle message of the test has no main rows over E");
        }
        if o.answers < 1 {
            return Some("an oracle message of the test is not sampled");
        }
    }
    if S.fold.u.mask_rows > 0 && S.fold.u.mask_code != S.shared_mask_code {
        return Some("the folded row's mask rows have another code than its group");
    }
    if S.w.mask_rows > 0 && S.w.mask_code != S.own_mask_code {
        return Some("W's mask rows have another code than its group");
    }
    if S.omega.mask_rows > 0 {
        return Some(
            "Omega has mask rows; it is a member of groups with different mask codes and may have main rows only",
        );
    }
    if S.shared_split_needed() && S.omega_leaf_class == S.shared_split_leaf_class {
        return Some("Omega and the shared split's mask message have one leaf class; they are read at different lists");
    }
    if S.own_split_needed() && S.w_leaf_class == S.own_split_leaf_class {
        return Some("W and a request's split's mask message have one leaf class; they are read at different lists");
    }
    for own in [false, true] {
        if !(if own { S.own_split_needed() } else { S.shared_split_needed() }) {
            continue;
        }
        let o = if own { &S.own_split } else { &S.shared_split };
        let mask_code = if own { S.own_mask_code } else { S.shared_mask_code };
        if o.main_rows != 0
            || o.mask_rows == 0
            || o.answers < 1
            || o.mask_code != mask_code
        {
            return Some("a split needs a sampled message of mask rows alone, under its groups' mask code");
        }
    }
    None
}

/// The same, with the codes that the shape names (`lin_fault`, lin.h:123-131). The first and
/// shared parts end the process on a fault: check a shape read from a file with this first.
pub fn lin_fault(codes: &Codes, S: &LinShape) -> Option<&'static str> {
    if let Some(f) = lin_public_fault(S) {
        return Some(f);
    }
    if let Some(f) = foldeq_fault(codes, &S.fold) {
        return Some(f);
    }
    if S.omega.code as usize >= codes.base.len() || S.w.code as usize >= codes.base.len() {
        return Some("an oracle message of the test names a code that is not there");
    }
    if S.shared_mask_code as usize >= codes.mask.len()
        || S.own_mask_code as usize >= codes.mask.len()
    {
        return Some("a group of the test names a mask code that is not there");
    }
    if S.matrix_rows > vector_room(codes, &S.omega, S.omega_rows_high) {
        return Some("Omega's layout runs into its pad");
    }
    if (1u64 << S.k_col()) > vector_room(codes, &S.w, S.w_rows_high) {
        return Some("W's layout runs into its pad");
    }
    None
}

/// The shape of the first fold of a test, as far as its fresh mask needs it (`lin_fold_shape`,
/// lin.h:134-139).
pub fn lin_fold_shape(test: &[IoppStage], leaf_class: u32) -> FoldShape {
    assert!(!test.is_empty(), "LIN: a test without stages");
    let mut F = iopp_fold_shape(&test[0], GroupLayout::default());
    F.mask_leaf_class = leaf_class;
    F
}

/// The oracle messages of W_c's prover message (`lin_message_w`, lin.h:143-148).
pub fn lin_message_w(S: &LinShape) -> Vec<OracleNotice> {
    let mut m = Vec::with_capacity(3);
    m.push(OracleNotice { shape: S.w.clone(), leaf_class: S.w_leaf_class });
    if S.own_split_needed() {
        m.push(OracleNotice {
            shape: S.own_split.clone(),
            leaf_class: S.own_split_leaf_class,
        });
    }
    if S.masks_ahead {
        m.push(fold_mask_notice(&lin_fold_shape(&S.test_own, S.w_leaf_class)));
    }
    m
}

/// The oracle messages of G_u's prover message (`lin_message_u`, lin.h:149-153).
pub fn lin_message_u(S: &LinShape) -> Vec<OracleNotice> {
    let mut m = Vec::with_capacity(2);
    m.push(OracleNotice { shape: S.fold.u.clone(), leaf_class: S.fold.leaf_class });
    if S.masks_ahead {
        m.push(fold_mask_notice(&lin_fold_shape(
            &S.test_u,
            S.fold.leaf_class,
        )));
    }
    m
}

/// The oracle messages of Omega's prover message (`lin_message_omega`, lin.h:154-158).
pub fn lin_message_omega(S: &LinShape) -> Vec<OracleNotice> {
    let mut m = Vec::with_capacity(2);
    m.push(OracleNotice { shape: S.omega.clone(), leaf_class: S.omega_leaf_class });
    if S.shared_split_needed() {
        m.push(OracleNotice {
            shape: S.shared_split.clone(),
            leaf_class: S.shared_split_leaf_class,
        });
    }
    m
}

fn put_stages(w: &mut Writer, st: &[IoppStage]) {
    w.put_u64(st.len() as u64);
    for s in st {
        s.public_bytes(w);
    }
}

impl PublicBytes for LinShape {
    /// `public_bytes(Writer&, const LinShape&)` (lin.h:160-167).
    fn public_bytes(&self, w: &mut Writer) {
        self.fold.public_bytes(w);
        w.put_u64(self.k_lo as u64);
        w.put_u64(self.matrix_rows);
        self.omega.public_bytes(w);
        self.w.public_bytes(w);
        w.put_u64(self.omega_rows_high as u64);
        w.put_u64(self.w_rows_high as u64);
        self.shared_split.public_bytes(w);
        self.own_split.public_bytes(w);
        for c in [
            self.omega_leaf_class,
            self.shared_split_leaf_class,
            self.w_leaf_class,
            self.own_split_leaf_class,
        ] {
            w.put_u64(c as u64);
        }
        w.put_u64(self.shared_mask_code as u64);
        w.put_u64(self.own_mask_code as u64);
        w.put_u64(self.masks_ahead as u64);
        for test in [&self.test_u, &self.test_omega, &self.test_own, &self.test_own_omega] {
            put_stages(w, test);
        }
        self.choice.public_bytes(w);
    }
    /// `public_fault(const LinShape&)` (lin.h:99-120).
    fn public_fault(&self) -> Option<&'static str> {
        lin_public_fault(self)
    }
}

// ------------------------------------------------------------------------------------------------
// LIN's public inputs and the binder
// ------------------------------------------------------------------------------------------------

/// LIN's public inputs as handles into a chain's first query (`LinPublic`, lin.h:171-176).
#[derive(Clone, Debug, Default)]
pub struct LinPublic {
    pub codes: Public<Codes>,
    pub shape: Public<LinShape>,
    pub table: Public<IndexName>,
    /// The shared chain only: the binding tree's places (from `lin_bind_shared`); else 0.
    pub places: u64,
}

/// Codes and shape are parameters (`lin_bind_parameters`, lin.h:183-185).
pub fn lin_bind_parameters(b: &mut Binder, codes: &Codes, S: &LinShape, x: &mut LinPublic) {
    x.codes = b.parameter("codes", codes.clone());
    x.shape = b.parameter("the test on the table", S.clone());
}

/// The first item of the statement (`lin_bind_table`, lin.h:187).
pub fn lin_bind_table(b: &mut Binder, table: &IndexName, x: &mut LinPublic) {
    x.table = b.statement("table", table.clone());
}

/// Both calls (`lin_bind`, lin.h:189-194).
pub fn lin_bind(b: &mut Binder, codes: &Codes, S: &LinShape, table: &IndexName) -> LinPublic {
    let mut x = LinPublic::default();
    lin_bind_parameters(b, codes, S, &mut x);
    lin_bind_table(b, table, &mut x);
    x
}

/// The shared chain: the binding tree's root takes the place of random bytes
/// (`lin_bind_shared`, lin.h:701-706).
pub fn lin_bind_shared(
    b: &mut Binder,
    codes: &Codes,
    S: &LinShape,
    table: &IndexName,
    binding_root: &LinBindingRoot,
) -> LinPublic {
    let mut x = lin_bind(b, codes, S, table);
    let root = b.statement("the binding tree's root", *binding_root.digest());
    b.random_bytes_are(&root);
    x.places = binding_root.places();
    x
}

/// A request's second chain follows both seals (`lin_bind_second`, lin.h:709-712).
pub fn lin_bind_second(b: &mut Binder, own: &Sealed, shared: &Sealed) {
    b.follows(own);
    b.follows(shared);
}

// ------------------------------------------------------------------------------------------------
// The linear claims
// ------------------------------------------------------------------------------------------------

/// One request's claim (`LinClaim`, lin.h:204-215):
/// `< g (x) eq(psi, .), M >  +  sum of coeff * (mask entry)  =  target`.
#[derive(Clone, Debug, Default)]
pub struct LinClaim {
    pub g: Vec<Tensor>,
    pub psi: Vec<E>,
    pub masks: Vec<Unit>,
    pub target: E,
}

impl LinClaim {
    /// Consumes the mask entry (`add_mask`, lin.h:210-214).
    pub fn add_mask(&mut self, slot: super::mask::MaskSlot, coeff: E) {
        let o = slot.oracle();
        let i = slot.index();
        self.masks.push(Unit { oracle: o, part: Part::Mask, index: i as u64, coeff });
    }
}

/// (Eval): W_c at psi_c + the claim's mask entries = tau_c (`lin_eval_row`, lin.h:230-238).
pub fn lin_eval_row(S: &LinShape, claim: &LinClaim, w: OracleId, w_lay: VectorLay) -> Row {
    assert!(
        claim.psi.len() == S.k_col() as usize,
        "LIN: a claim's point has one coordinate for each column bit"
    );
    let mut row = Row::plain("LIN: the claim on W");
    row.units = claim.masks.clone();
    row.target = claim.target;
    row.add(w, Part::Main, w_lay.on_table(Tensor::eq(&claim.psi, S.k_col(), E::one())));
    row
}

/// (Fold): Omega at zeta = `< eq(psi_lo, .) (x) eq(zeta, .), u >` (`lin_fold_row`, lin.h:240-253).
pub fn lin_fold_row(
    S: &LinShape,
    psi: &[E],
    zeta: &[E],
    u: &FoldedRow,
    omega: OracleId,
    omega_lay: VectorLay,
) -> Row {
    let mut row = Row::plain("LIN: Omega against the folded row");
    let mut cut = Vec::new();
    tensor_below(
        &Tensor::eq(zeta, S.k_row(), E::one()),
        0,
        S.k_row(),
        S.matrix_rows,
        &mut cut,
    );
    for t in cut.drain(..) {
        row.add(omega, Part::Main, omega_lay.on_table(t));
    }
    let mut on_u = Tensor::eq(psi, S.k_lo, -E::one());
    for t in 0..S.k_row() as usize {
        on_u.push(E::one() - zeta[t], zeta[t]);
    }
    tensor_below(&on_u, S.k_lo, S.k_row(), S.matrix_rows, &mut cut);
    for t in cut.drain(..) {
        row.add(u.oracle, Part::Main, u.lay.on_table(t));
    }
    row
}

/// (Dot): `< g_c, Omega >` = W_c at psi* (`lin_dot_row`, lin.h:257-269).
pub fn lin_dot_row(
    S: &LinShape,
    weights: &[Tensor],
    psi: &[E],
    omega: OracleId,
    omega_lay: VectorLay,
    w: OracleId,
    w_lay: VectorLay,
) -> Row {
    let mut row = Row::plain("LIN: the row weights on Omega against W at the shared point");
    let mut cut = Vec::new();
    for g in weights {
        assert!(
            g.vars() == S.k_row(),
            "LIN: row weights have one variable for each row bit"
        );
        tensor_below(g, 0, S.k_row(), S.matrix_rows, &mut cut);
    }
    for t in cut.drain(..) {
        row.add(omega, Part::Main, omega_lay.on_table(t));
    }
    row.add(w, Part::Main, w_lay.on_table(Tensor::eq(psi, S.k_col(), -E::one())));
    row
}

// ------------------------------------------------------------------------------------------------
// First part: a request by itself
// ------------------------------------------------------------------------------------------------

/// What the first part leaves for the second (`LinFirst`, lin.h:341-346).
#[derive(Debug)]
pub struct LinFirst {
    pub w: OracleId,
    pub split: OracleId,
    /// The request's own group.
    pub own: GroupId,
    /// Of the first fold of the test on that group, if sent with W_c.
    pub mask: FoldMask,
    pub claim: LinClaim,
}

impl Default for LinFirst {
    /// Rust's derive would give 0, but the C++ defaults are NONE_ID (lin.h:342-343).
    fn default() -> Self {
        LinFirst {
            w: NONE_ID,
            split: NONE_ID,
            own: NONE_ID,
            mask: FoldMask::default(),
            claim: LinClaim::default(),
        }
    }
}

/// The rows of the first part (`lin_first_rows`, lin.h:348-361).
pub fn lin_first_rows(
    st: &mut Statement,
    S: &LinShape,
    claim: LinClaim,
    ids: &[OracleId],
    out: &mut LinFirst,
) {
    out.w = ids[0];
    out.claim = claim;
    out.own = st.new_group("LIN: a request's own rows", S.w.code, S.own_mask_code);
    let mut inputs: Vec<OracleId> = out.claim.masks.iter().map(|u| u.oracle).collect();
    inputs.sort_unstable();
    inputs.dedup();
    for o in inputs {
        st.join(out.own, o, false);
    }
    st.join(out.own, out.w, false);
    if S.own_split_needed() {
        out.split = ids[1];
        st.join(out.own, out.split, false);
    }
    if S.masks_ahead {
        out.mask.sent_as(*ids.last().unwrap());
    }
    let lay = vector_lay(st.codes(), &S.w, S.w_rows_high);
    let row = lin_eval_row(S, &out.claim, out.w, lay);
    st.add_row(out.own, row);
}

/// The verifier's first part (`lin_first_verify_on_shape`, lin.h:382-394).
pub fn lin_first_verify_on_shape(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &LinShape,
    claim: LinClaim,
    out: &mut LinFirst,
    calls: &mut HashCalls,
) -> bool {
    if let Some(f) = lin_fault(V.st.codes(), S) {
        panic!("{}", f); // a bad shape is the caller's fault, not a proof's
    }
    let (good, ids) = send_verify(V, &lin_message_w(S), AnswersRound::Own, calls);
    if !good {
        return false;
    }
    lin_first_rows(&mut V.st, S, claim, &ids, out);
    if V.notes.is_some() {
        // Values for comparing a second verifier block by block; no check reads them.
        let lay = vector_lay(V.st.codes(), &S.w, S.w_rows_high);
        let target = out.claim.target;
        V.note("LIN: (Eval)'s target", target);
        let on_w = lin_eval_row(S, &out.claim, out.w, lay)
            .coefficient(out.w, Part::Main, lay.index(1));
        V.note("LIN: (Eval) on W<1>", on_w);
    }
    true
}

/// `lin_first_verify` (lin.h:718-720).
pub fn lin_first_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    x: &LinPublic,
    claim: LinClaim,
    out: &mut LinFirst,
    calls: &mut HashCalls,
) -> bool {
    let S = V.ch.get(&x.shape).clone();
    lin_first_verify_on_shape(V, &S, claim, out, calls)
}

// ------------------------------------------------------------------------------------------------
// Shared part: once for a batch
// ------------------------------------------------------------------------------------------------

/// What the shared part leaves (`LinShared`, lin.h:418-425); `psi` is psi*.
#[derive(Debug)]
pub struct LinShared {
    pub psi: Vec<E>,
    pub zeta: Vec<E>,
    pub u: FoldedRow,
    pub omega: OracleId,
    pub split: OracleId,
    pub group_u: GroupId,
    pub group_omega: GroupId,
    /// Of the first fold of the test on G_u's group, if sent with G_u.
    pub mask: FoldMask,
    /// The shared chain's inputs; set by `lin_shared_verify`.
    pub bound: LinPublic,
}

impl Default for LinShared {
    /// The C++ member defaults (lin.h:419-424).
    fn default() -> Self {
        LinShared {
            psi: Vec::new(),
            zeta: Vec::new(),
            u: FoldedRow::default(),
            omega: NONE_ID,
            split: NONE_ID,
            group_u: NONE_ID,
            group_omega: NONE_ID,
            mask: FoldMask::default(),
            bound: LinPublic::default(),
        }
    }
}

/// Draws a round's elements of E (`lin_draw`, lin.h:427-432).
pub fn lin_draw(
    ch: &mut VerifierRounds<'_, '_, '_>,
    round: &str,
    count: usize,
    calls: &mut HashCalls,
) -> Vec<E> {
    let mut from = ch.close_algebraic(round, calls);
    let mut x = Vec::with_capacity(count);
    for _ in 0..count {
        x.push(from.draw(calls));
    }
    x
}

/// The shared part's two groups (`lin_shared_groups`, lin.h:433-436).
pub fn lin_shared_groups(st: &mut Statement, S: &LinShape, out: &mut LinShared) {
    out.group_u = st.new_group("LIN: the folded row", S.fold.u.code, S.shared_mask_code);
    out.group_omega = if S.shared_split_needed() {
        st.new_group("LIN: Omega", S.omega.code, S.shared_mask_code)
    } else {
        out.group_u
    };
}

/// What shares a leaf is read at exactly the same lists; Omega is read at 1 + N lists
/// (`lin_alone_in_its_tree`, lin.h:444).
pub fn lin_alone_in_its_tree(book: &TreeBook, o: OracleId) -> bool {
    book.tree(book.place(o).tree).parts.len() == 1
}

/// Joins Omega and, where a split is needed, its mask message (`lin_shared_join`, lin.h:446-452).
pub fn lin_shared_join(
    st: &mut Statement,
    book: &TreeBook,
    S: &LinShape,
    ids: &[OracleId],
    out: &mut LinShared,
) {
    assert!(
        lin_alone_in_its_tree(book, ids[0]),
        "LIN: something rides in Omega's leaves, which every request's test opens"
    );
    out.omega = ids[0];
    st.join(out.group_omega, out.omega, false);
    if !S.shared_split_needed() {
        return;
    }
    out.split = ids[1];
    st.join(out.group_omega, out.split, false);
    st.join(out.group_u, out.split, false);
}

/// The verifier's shared part (`lin_shared_verify_on_shape`, lin.h:522-549).
pub fn lin_shared_verify_on_shape(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &LinShape,
    places: u64,
    test: TableTest,
    table: &TableRead<'_>,
    out: &mut LinShared,
    calls: &mut HashCalls,
) -> bool {
    if let Some(f) = lin_fault(V.st.codes(), S) {
        panic!("{}", f);
    }
    assert!(
        test != TableTest::Link,
        "LIN: a test on the table is the one-time test or a later one"
    );
    out.psi = lin_draw(V.ch, R_LIN_POINT, S.k_col() as usize, calls);
    V.ch.require_table(&priced_table(&S.fold.index, test));
    V.ch.require_sharing(places);
    lin_shared_groups(&mut V.st, S, out);
    let mut with = lin_message_u(S);
    with.remove(0);
    let mut with_ids = Vec::new();
    let gamma = &out.psi[S.k_lo as usize..];
    if !foldeq_verify(
        V,
        table,
        &S.fold,
        test,
        gamma,
        out.group_u,
        &mut out.u,
        &with,
        Some(&mut with_ids),
        calls,
    ) {
        return false;
    }
    if S.masks_ahead {
        out.mask.sent_as(with_ids[0]);
    }

    let (good, ids) = send_verify(V, &lin_message_omega(S), AnswersRound::Own, calls);
    if !good {
        return false;
    }
    lin_shared_join(&mut V.st, &V.book, S, &ids, out);

    out.zeta = lin_draw(V.ch, R_LIN_ZETA, S.k_row() as usize, calls);
    let omega_lay = vector_lay(V.st.codes(), &S.omega, S.omega_rows_high);
    let row = lin_fold_row(S, &out.psi, &out.zeta, &out.u, out.omega, omega_lay);
    if V.notes.is_some() {
        let on_omega = row.coefficient(out.omega, Part::Main, omega_lay.index(0));
        let on_u = row.coefficient(out.u.oracle, Part::Main, out.u.lay.index(1));
        V.note("LIN: (Fold) on Omega<0>", on_omega);
        V.note("LIN: (Fold) on G_u<1>", on_u);
    }
    if S.shared_split_needed() {
        return split_verify(
            V.ch,
            &mut V.st,
            &row,
            out.group_omega,
            out.group_u,
            out.split,
            calls,
        );
    }
    V.st.add_row(out.group_u, row);
    V.ch.ok()
}

/// The shared part's proximity tests (`lin_shared_tests_verify_on_shape`, lin.h:566-569).
pub fn lin_shared_tests_verify_on_shape(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &LinShape,
    x: &mut LinShared,
    calls: &mut HashCalls,
) -> bool {
    let mask = core::mem::take(&mut x.mask);
    if !iopp_verify(V, x.group_u, &S.test_u, S.choice, mask, calls) {
        return false;
    }
    !S.shared_split_needed()
        || iopp_verify(
            V,
            x.group_omega,
            &S.test_omega,
            S.choice,
            FoldMask::default(),
            calls,
        )
}

/// `lin_shared_tests_verify` (lin.h:749).
pub fn lin_shared_tests_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    x: &LinPublic,
    s: &mut LinShared,
    calls: &mut HashCalls,
) -> bool {
    let S = V.ch.get(&x.shape).clone();
    lin_shared_tests_verify_on_shape(V, &S, s, calls)
}

/// `lin_shared_verify` (lin.h:738-746): the bound table's key and configuration are checked
/// before the shape's body runs.
pub fn lin_shared_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    x: &LinPublic,
    test: TableTest,
    table: &TableRead<'_>,
    out: &mut LinShared,
    calls: &mut HashCalls,
) -> bool {
    let key = table.reader();
    {
        let name = V.ch.get(&x.table);
        assert!(
            key.commitment() == name.commitment
                && super::foldeq::record_bytes(key.record())
                    == super::foldeq::record_bytes(&name.record),
            "LIN: the key is another table's than the chain's first query names"
        );
        assert!(
            key.configuration() == *V.ch.configuration(),
            "LIN: the table's tree starts from another configuration's digest than the chain names"
        );
    }
    out.bound = x.clone();
    let S = V.ch.get(&x.shape).clone();
    lin_shared_verify_on_shape(V, &S, x.places, test, table, out, calls)
}

// ------------------------------------------------------------------------------------------------
// Second part: a request by itself, on a chain that follows its first chain and the shared chain
// ------------------------------------------------------------------------------------------------

/// Enters an oracle message sent and sampled on another chain (`lin_adopt`, lin.h:584-592).
pub fn lin_adopt(
    st: &mut Statement,
    book: &mut TreeBook,
    from_st: &Statement,
    from_book: &TreeBook,
    theirs: OracleId,
    leaf_class: u32,
) -> OracleId {
    assert!(
        lin_alone_in_its_tree(from_book, theirs),
        "LIN: an oracle message that several chains read has a tree of its own"
    );
    let tree = from_book.tree(from_book.place(theirs).tree);
    let notices = [OracleNotice { shape: from_st.oracle(theirs).shape.clone(), leaf_class }];
    let mut ids = Vec::new();
    let mine = book.enter(st, &notices, &mut ids);
    book.adopt(mine, tree); // keeps its sender's tree number and run's value
    st.sampled_elsewhere(ids[0], from_st, theirs);
    ids[0]
}

/// What the second part leaves for its tests (`LinSecond`, lin.h:595-598).
#[derive(Clone, Copy, Debug)]
pub struct LinSecond {
    pub omega: OracleId,
    /// `LinFirst::own`, or a second group if W and Omega differ in code.
    pub around_omega: GroupId,
}

impl Default for LinSecond {
    /// The C++ member defaults are NONE_ID (lin.h:596-597).
    fn default() -> Self {
        LinSecond { omega: NONE_ID, around_omega: NONE_ID }
    }
}

/// The rows of the second part (`lin_second_rows`, lin.h:600-606).
pub fn lin_second_rows(
    st: &mut Statement,
    S: &LinShape,
    first: &LinFirst,
    weights: &[Tensor],
    shared: &LinShared,
    out: &mut LinSecond,
) -> Row {
    out.around_omega = if S.own_split_needed() {
        st.new_group("LIN: a request's rows on Omega", S.omega.code, S.own_mask_code)
    } else {
        first.own
    };
    st.join(out.around_omega, out.omega, false);
    if S.own_split_needed() {
        st.join(out.around_omega, first.split, false);
    }
    let omega_lay = vector_lay(st.codes(), &S.omega, S.omega_rows_high);
    let w_lay = vector_lay(st.codes(), &S.w, S.w_rows_high);
    lin_dot_row(S, weights, &shared.psi, out.omega, omega_lay, first.w, w_lay)
}

/// The verifier's second part (`lin_second_verify_on_shape`, lin.h:623-634).
pub fn lin_second_verify_on_shape(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &LinShape,
    first: &LinFirst,
    shared_V: &VerifierContext<'_, '_, '_, '_>,
    shared: &LinShared,
    out: &mut LinSecond,
    calls: &mut HashCalls,
) -> bool {
    out.omega = lin_adopt(
        &mut V.st,
        &mut V.book,
        &shared_V.st,
        &shared_V.book,
        shared.omega,
        S.omega_leaf_class,
    );
    let row = lin_second_rows(&mut V.st, S, first, &first.claim.g, shared, out);
    if V.notes.is_some() {
        let omega_lay = vector_lay(V.st.codes(), &S.omega, S.omega_rows_high);
        let w_lay = vector_lay(V.st.codes(), &S.w, S.w_rows_high);
        let on_omega = row.coefficient(out.omega, Part::Main, omega_lay.index(0));
        let on_w = row.coefficient(first.w, Part::Main, w_lay.index(1));
        V.note("LIN: (Dot) on Omega<0>", on_omega);
        V.note("LIN: (Dot) on W<1>", on_w);
    }
    if S.own_split_needed() {
        return split_verify(
            V.ch,
            &mut V.st,
            &row,
            out.around_omega,
            first.own,
            first.split,
            calls,
        );
    }
    V.st.add_row(first.own, row);
    V.ch.ok()
}

/// `lin_second_verify` (lin.h:768-773).
pub fn lin_second_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    x: &LinPublic,
    first: &LinFirst,
    shared_V: &VerifierContext<'_, '_, '_, '_>,
    shared: &LinShared,
    out: &mut LinSecond,
    calls: &mut HashCalls,
) -> bool {
    assert!(
        V.ch.stands_on(shared_V.ch),
        "LIN: the second chain's first query does not hold the seal of the shared chain that is handed in"
    );
    assert!(
        lin_same_public(V.ch, x, &shared.bound),
        "LIN: the request's first chain and the shared chain hold different codes, shapes or tables"
    );
    let S = V.ch.get(&x.shape).clone();
    lin_second_verify_on_shape(V, &S, first, shared_V, shared, out, calls)
}

/// The second part's proximity tests (`lin_second_tests_verify_on_shape`, lin.h:648-651).
pub fn lin_second_tests_verify_on_shape(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &LinShape,
    first: &mut LinFirst,
    x: &LinSecond,
    calls: &mut HashCalls,
) -> bool {
    let mask = core::mem::take(&mut first.mask);
    if !iopp_verify(V, first.own, &S.test_own, S.choice, mask, calls) {
        return false;
    }
    !S.own_split_needed()
        || iopp_verify(
            V,
            x.around_omega,
            &S.test_own_omega,
            S.choice,
            FoldMask::default(),
            calls,
        )
}

/// `lin_second_tests_verify` (lin.h:778-780).
pub fn lin_second_tests_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    x: &LinPublic,
    first: &mut LinFirst,
    second: &LinSecond,
    calls: &mut HashCalls,
) -> bool {
    let S = V.ch.get(&x.shape).clone();
    lin_second_tests_verify_on_shape(V, &S, first, second, calls)
}

// ------------------------------------------------------------------------------------------------
// How the chains of a batch are tied together
// ------------------------------------------------------------------------------------------------

/// Codes, shape and table are in the first query of both chains; here they are compared
/// (`lin_same_public`, lin.h:753-758).
pub fn lin_same_public(
    ch: &VerifierRounds<'_, '_, '_>,
    a: &LinPublic,
    b: &LinPublic,
) -> bool {
    let mut first = Writer::default();
    ch.get(&a.codes).public_bytes(&mut first);
    ch.get(&a.shape).public_bytes(&mut first);
    ch.get(&a.table).public_bytes(&mut first);
    let mut second = Writer::default();
    ch.get(&b.codes).public_bytes(&mut second);
    ch.get(&b.shape).public_bytes(&mut second);
    ch.get(&b.table).public_bytes(&mut second);
    first.bytes() == second.bytes()
}

// ------------------------------------------------------------------------------------------------
// The binding tree
// ------------------------------------------------------------------------------------------------

/// 2^log_leaves leaves, each a hash of a seal and a salt (`LinBindingShape`, lin.h:802-805).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LinBindingShape {
    pub log_leaves: u32,
    pub salt_bytes: usize,
}

impl Default for LinBindingShape {
    fn default() -> Self {
        LinBindingShape { log_leaves: 0, salt_bytes: 40 }
    }
}

impl PublicBytes for LinBindingShape {
    /// `public_bytes(Writer&, const LinBindingShape&)` (lin.h:806).
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.log_leaves as u64);
        w.put_u64(self.salt_bytes as u64);
    }
    /// `public_fault(const LinBindingShape&)` (lin.h:807-811).
    fn public_fault(&self) -> Option<&'static str> {
        if self.log_leaves > 48 {
            return Some("the binding tree is too deep");
        }
        if !salt_length_fits(self.salt_bytes as u64) {
            return Some("the binding tree's salts have no admitted length");
        }
        None
    }
}

/// A binding tree's root and the number of its places (`LinBindingRoot`, lin.h:682-697).
#[derive(Clone, Copy, Debug, Default)]
pub struct LinBindingRoot {
    digest: Digest,
    places: u64,
}

impl LinBindingRoot {
    /// `digest()` (lin.h:685).
    pub fn digest(&self) -> &Digest {
        &self.digest
    }
    /// `places()` (lin.h:686).
    pub fn places(&self) -> u64 {
        self.places
    }
    /// For a test or benchmark that runs the shared part alone, without requests or a tree
    /// (`made_up_without_a_tree`, lin.h:689).
    pub fn made_up_without_a_tree(digest: Digest, places: u64) -> Self {
        LinBindingRoot { digest, places }
    }
}

/// A vertex hashes its two children only (`lin_binding_vertex`, lin.h:816-818).
pub fn lin_binding_vertex(
    configuration: &Digest,
    left: &Digest,
    right: &Digest,
    calls: &mut HashCalls,
) -> Digest {
    vertex(
        &Tag::vertex(Domain::BindingNode, 0, configuration),
        left,
        right,
        calls,
    )
}

/// A leaf is bound to its place (`lin_binding_leaf`, lin.h:819-821).
pub fn lin_binding_leaf(
    s: &LinBindingShape,
    configuration: &Digest,
    place: u64,
    seal: &Digest,
    salt: &[u8],
    calls: &mut HashCalls,
) -> Digest {
    leaf_digest(
        &Tag::leaf(
            Domain::LeafBinding,
            0,
            configuration,
            4,
            s.salt_bytes as u64,
        ),
        tree_index(s.log_leaves, place),
        seal,
        salt,
        calls,
    )
}

/// The root that a request's seal and its path lead to (`lin_binding_root`, lin.h:873-886).
/// False if the place is out of range or bytes are missing.
pub fn lin_binding_root(
    r: &mut Reader<'_>,
    s: &LinBindingShape,
    configuration: &Digest,
    seal: &Digest,
    out: &mut LinBindingRoot,
    calls: &mut HashCalls,
) -> bool {
    let mut place = match r.get_u64() {
        Some(p) => p,
        None => return false,
    };
    if (place >> s.log_leaves) != 0 {
        r.refuse();
        return false;
    }
    let salt = match r.take(s.salt_bytes) {
        Some(x) => x,
        None => return false,
    };
    let mut root = lin_binding_leaf(s, configuration, place, seal, salt, calls);
    let mut d = s.log_leaves;
    while d > 0 {
        let sibling = match r.get_digest() {
            Some(x) => x,
            None => return false,
        };
        root = if place & 1 == 1 {
            lin_binding_vertex(configuration, &sibling, &root, calls)
        } else {
            lin_binding_vertex(configuration, &root, &sibling, calls)
        };
        place >>= 1;
        d -= 1;
    }
    *out = LinBindingRoot { digest: root, places: 1u64 << s.log_leaves };
    true
}
