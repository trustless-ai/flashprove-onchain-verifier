//! The checks of a whole proof file, ported from `blocks/frame/check.h`.
//!
//! `check_proof` builds the first queries of a proof file's three hash chains, checks the request's
//! own parts and hands the segments to the caller's callback (`LinksCheck`). Both sides take a
//! `Configured`; the committed table must have passed `check_key` or `check_entry`, or, for the
//! split-process form, `check_proof_if_tested`.
//!
//! Ported: `RequestPublic`, `bind_request_parameters`, `bind_request_statement`,
//! `bind_shared_chain`, `bind_second_chain`, `LinksResult`, `LinksCheck`, `MoreParameters`,
//! `ProofFacts`, `check_proof` and `check_proof_if_tested`.
//!
//! Deviations at the verifier's boundary:
//! - `LinksCheck` and `MoreParameters` are `dyn` aliases, the port's form of C++'s
//!   `std::function`.
//! - `VerifierRounds` owns its borrows of the proof reader and the session, so two channels cannot
//!   be live at once. After a chain's last check its `Statement` and `TreeBook` are moved out and
//!   the channel is sealed; the second chain's context is rebuilt around them (`continue_chain`).
//!   `VerifierContext::goes_on`'s first assertion (`later.stands_on(self.ch)`) is kept
//!   structurally: `lin_bind_second` makes the second chain follow the first chain's seal and the
//!   shared chain's seal before the channel is built.
//! - `check_proof` in C++ has no notes parameter; the callback owns its context's notes. The same
//!   here.

#![allow(non_snake_case)] // the C++ names `V`, `first_V`, `shared_V`

use alloc::string::String;
use alloc::vec::Vec;

use crate::chain::public::{Binder, Public, Sealed};
use crate::chain::rounds::VerifierRounds;
use crate::chain::session::VerifierSession;
use crate::field::ext::E;
use crate::frame::configure::{Configured, ProofVerdict};
use crate::frame::heads::{
    read_head_entry, HEAD_TAG_PROOF, LABEL_FIRST_CHAIN, LABEL_PROOF_SECOND_CHAIN,
    LABEL_PROOF_SHARED_CHAIN,
};
use crate::frame::key_fixed::{key_fixed, key_public_bytes};
use crate::hash::calls::HashCalls;
use crate::hash::modes::Digest;
use crate::iop::batt::TensorRow;
use crate::iop::context::{TreeBook, VerifierContext};
use crate::iop::foldeq::{
    vector_lay, IfTested, IndexName, IndexReader, TableRead, TestedTable, UnprovedTable,
    IF_TESTED_WHY,
};
use crate::iop::lin::{
    lin_adopt, lin_bind_parameters, lin_bind_second, lin_bind_shared, lin_bind_table,
    lin_second_rows, lin_same_public, LinBindingRoot, LinBindingShape, LinFirst, LinPublic,
    LinSecond, LinShared,
};
use crate::iop::member::member_first_verify;
use crate::iop::message::Reader;
use crate::iop::relation::{Statement, NONE_ID, OracleId, Part};
use crate::iop::req::ReqShape;
use crate::iop::req_rows::ReqLayout;
use crate::iop::split::split_verify;
use crate::numbers::plan::{Planned, TableTest};
use crate::numbers::round_names::R_SEAL;

/// A word of a chain, as the port's `VerifierRounds` names it. The C++ caller keeps a pointer into
/// a `std::vector`; the port appends a copy of the same pairs.
pub type Notes = Vec<(String, E)>;

/// `does_not_hold`'s fixed sentence (plan.h:634-637). C++ also prints the plan's first cause to
/// stderr; a `no_std` core has no stderr, and the cause stays on the plan (`Planned::why_not`).
pub const DOES_NOT_HOLD_WHY: &str =
    "the parameters are not admitted (the first cause is on stderr)";

/// `does_not_hold` (plan.h:632-637): a reason for a caller whose message has no room for the
/// cause. The cause itself is `p.why_not()`.
pub fn does_not_hold(_p: &Planned, _who: &str) -> &'static str {
    DOES_NOT_HOLD_WHY
}

/// A chain's context minus its channel (`VerifierContext`'s statement and tree book).
pub(crate) struct ChainState {
    pub st: Statement,
    pub book: TreeBook,
}

/// Copies the caller's notes into a context's own store (`VerifierContext::notes` is owned here,
/// where C++ keeps a pointer). The values are copied back with `notes_done`.
pub(crate) fn notes_start(notes: Option<&mut Notes>) -> Option<Notes> {
    notes.map(|n| (*n).clone())
}

/// Appends the values that a context collected to the caller's vector, in order.
pub(crate) fn notes_done(notes: Option<&mut Notes>, from: &mut Option<Notes>) {
    if let (Some(to), Some(from)) = (notes, from.take()) {
        let keep = to.len();
        if from.len() > keep {
            to.extend(from.into_iter().skip(keep));
        }
    }
}

/// Moves a context's statement and tree book out, ending its borrow of the channel.
pub(crate) fn take_chain_state(v: VerifierContext<'_, '_, '_, '_>) -> ChainState {
    let VerifierContext { st, book, .. } = v;
    ChainState { st, book }
}

/// The verifier's `lin_go_on` move (`VerifierContext(VerifierContext&&, ...)`, context.h:530-534)
/// for a context rebuilt around a later chain. The C++ assertion that the later chain follows the
/// earlier one is structural here: the caller binds the later chain to the earlier chain's seal.
pub(crate) fn continue_chain<'y, 'b, 'e, 'f>(
    state: ChainState,
    later: &'y mut VerifierRounds<'b, 'e, 'f>,
    notes: Option<&mut Notes>,
) -> VerifierContext<'y, 'b, 'e, 'f> {
    let ChainState { st, mut book } = state;
    assert!(
        later.plan().set.salt_bytes as usize == book.salt_bytes(),
        "context: the two chains' plans differ in the length of a salt"
    );
    book.goes_on(later.run());
    let mut v = VerifierContext { st, ch: later, book, notes: notes_start(notes) };
    v.st.has_no_engine();
    v
}

/// `lin_second_verify` (lin.h:768-773) for a shared context whose channel has been dropped. The
/// statement and tree book are the shared chain's; the second chain adopts Omega from them.
///
/// The C++ function's first assertion, `V.ch.stands_on(shared_V.ch)`, is structural here: the
/// second chain's `Binder` follows the shared chain's seal (`lin_bind_second`) before the channel
/// is made, so the shared chain's mark stands in the second chain's first query.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lin_second_verify_with(
    v: &mut VerifierContext<'_, '_, '_, '_>,
    x: &LinPublic,
    first: &LinFirst,
    shared_st: &Statement,
    shared_book: &TreeBook,
    shared: &LinShared,
    out: &mut LinSecond,
    calls: &mut HashCalls,
) -> bool {
    assert!(
        lin_same_public(v.ch, x, &shared.bound),
        "LIN: the request's first chain and the shared chain hold different codes, shapes or tables"
    );
    let s = v.ch.get(&x.shape).clone();
    out.omega = lin_adopt(
        &mut v.st,
        &mut v.book,
        shared_st,
        shared_book,
        shared.omega,
        s.omega_leaf_class,
    );
    let row = lin_second_rows(&mut v.st, &s, first, &first.claim.g, shared, out);
    if v.notes.is_some() {
        let omega_lay = vector_lay(v.st.codes(), &s.omega, s.omega_rows_high);
        let w_lay = vector_lay(v.st.codes(), &s.w, s.w_rows_high);
        let on_omega = row.coefficient(out.omega, Part::Main, omega_lay.index(0));
        let on_w = row.coefficient(first.w, Part::Main, w_lay.index(1));
        v.note("LIN: (Dot) on Omega<0>", on_omega);
        v.note("LIN: (Dot) on W<1>", on_w);
    }
    if s.own_split_needed() {
        return split_verify(
            v.ch,
            &mut v.st,
            &row,
            out.around_omega,
            first.own,
            first.split,
            calls,
        );
    }
    v.st.add_row(first.own, row);
    v.ch.ok()
}

/// Sets a rejection's place, if the caller asked for it.
pub(crate) fn set_place(
    at: &mut Option<&mut Option<&'static str>>,
    where_: Option<&'static str>,
) {
    if let Some(slot) = at.as_deref_mut() {
        *slot = where_;
    }
}

// ------------------------------------------------------------------------------------------------
// The public inputs of a request's first chain
// ------------------------------------------------------------------------------------------------

/// The public inputs of a request's first chain (`RequestPublic`, check.h:48-59). The parameters
/// come first; the committed table, the entry and the request follow in the statement.
#[derive(Default)]
pub struct RequestPublic {
    pub configuration: Public<Digest>,
    pub lin: LinPublic,
    pub shape: Public<ReqShape>,
    pub layout: Public<ReqLayout>,
    pub identifiers: Public<Vec<u64>>,
    pub pending_rows: Public<u64>,
    pub binding: Public<LinBindingShape>,
    pub entry: Public<u64>,
    pub request: Public<Vec<u8>>,
    /// The caller's request itself, byte for byte; `request` may hold it only as a digest.
    pub file_words: Public<Vec<u8>>,
}

/// `bind_request_parameters` (check.h:60-71).
pub fn bind_request_parameters(b: &mut Binder, c: &Configured) -> RequestPublic {
    let f = c.fixed();
    let mut x = RequestPublic::default();
    x.configuration = b.configuration(&f.configuration);
    lin_bind_parameters(b, &f.codes, &f.lin, &mut x.lin);
    x.shape = b.parameter("request's shape", f.shape.clone());
    x.layout = b.parameter("layout", f.layout.clone());
    x.identifiers = b.parameter("links' identifiers", f.identifiers.clone());
    x.pending_rows = b.parameter("pending rows", f.pending_rows);
    x.binding = b.parameter("binding tree", f.binding);
    x
}

/// `bind_request_statement` (check.h:73-78). The first item closes the parameters.
pub fn bind_request_statement(
    b: &mut Binder,
    x: &mut RequestPublic,
    table: &IndexName,
    entry: u32,
    request: &[u8],
    file_words: &[u8],
) {
    lin_bind_table(b, table, &mut x.lin);
    x.entry = b.statement("stored copy", entry as u64);
    x.request = b.statement("request", request.to_vec());
    x.file_words = b.statement("the request file's words", file_words.to_vec());
}

/// `bind_shared_chain` (check.h:81-84).
pub fn bind_shared_chain(
    b: &mut Binder,
    c: &Configured,
    table: &IndexName,
    binding_root: &LinBindingRoot,
) -> LinPublic {
    b.configuration(&c.fixed().configuration);
    lin_bind_shared(b, &c.fixed().codes, &c.fixed().lin, table, binding_root)
}

/// `bind_second_chain` (check.h:85-88).
pub fn bind_second_chain(b: &mut Binder, c: &Configured, own: &Sealed, shared: &Sealed) {
    b.configuration(&c.fixed().configuration);
    lin_bind_second(b, own, shared);
}

// ------------------------------------------------------------------------------------------------
// The caller's callbacks and the facts of an accepted proof
// ------------------------------------------------------------------------------------------------

/// What the caller's callback leaves (`LinksResult`, check.h:99-104). `check_proof` ends the
/// process if the callback accepts without a reply, with another number of pending rows than the
/// parameter `pending_rows`, or after changing the configuration's public bytes.
pub struct LinksResult {
    pub index_masks: OracleId,
    pub pending: Vec<TensorRow>,
    pub replied: bool,
    pub reply: E,
}

impl Default for LinksResult {
    /// The C++ member defaults: no mask message (NONE_ID, not 0), no reply yet.
    fn default() -> Self {
        LinksResult { index_masks: NONE_ID, pending: Vec::new(), replied: false, reply: E::zero() }
    }
}

impl LinksResult {
    /// The C++ member defaults: no mask message, no reply yet.
    pub fn new() -> Self {
        LinksResult::default()
    }
}

/// The caller's check of the request's segments (`LinksCheck`, check.h:105). It must check all the
/// segments, the proximity test after the last, and any rounds planned by
/// `Subproofs::after_links`.
pub type LinksCheck<'c> = dyn for<'x, 'a, 'd, 's> FnMut(
        &mut VerifierContext<'x, 'a, 'd, 's>,
        &RequestPublic,
        &mut LinksResult,
        &mut crate::hash::calls::HashCalls,
    ) -> bool
    + 'c;

/// Further parameters of the first chain (`MoreParameters`, check.h:106).
pub type MoreParameters<'c> = dyn FnMut(&mut Binder) + 'c;

/// What a caller may print of an accepted proof (`ProofFacts`, check.h:110-113).
#[derive(Clone, Copy, Debug, Default)]
pub struct ProofFacts {
    /// The first chain's last value; it differs from run to run because the prover draws a new
    /// chain salt for each.
    pub seal: Digest,
    /// The request's place in its batch.
    pub place: u64,
}

// ------------------------------------------------------------------------------------------------
// The check
// ------------------------------------------------------------------------------------------------

/// A rejection's `why`, `at` and verdict for `check_proof` (`no`, check.h:149).
fn no(
    ch: &VerifierRounds<'_, '_, '_>,
    why: &mut Option<&'static str>,
    at: &mut Option<&mut Option<&'static str>>,
    where_: &'static str,
) -> ProofVerdict {
    set_place(at, Some(where_));
    *why = Some(ch.why().unwrap_or(where_));
    ProofVerdict::No
}

/// `check_proof` (check.h:143-217).
#[allow(clippy::too_many_arguments)]
pub fn check_proof(
    c: &Configured,
    tested: &TestedTable,
    entry: u32,
    request: &[u8],
    file_words: &[u8],
    reply: &E,
    file: &mut Reader<'_>,
    links: &mut LinksCheck<'_>,
    more: Option<&mut MoreParameters<'_>>,
    calls: &mut HashCalls,
    why: &mut Option<&'static str>,
    facts: Option<&mut ProofFacts>,
    at: Option<&mut Option<&'static str>>,
) -> ProofVerdict {
    let mut at = at;
    let same_key_values =
        || tested.key_public() == key_public_bytes(&key_fixed(c.sized(), c.configuration()));
    set_place(&mut at, Some("before the chains"));
    if !c.refused().is_empty() {
        *why = Some("the public files are not admitted");
        return ProofVerdict::No;
    }
    // NO, not the end of the process: a rejection can depend on a file's bytes.
    if tested.tested_under().is_none() {
        *why = Some("the table has passed no check: its key or entry was refused, or was never checked");
        return ProofVerdict::No;
    }
    assert!(
        same_key_values(),
        "check_proof: the table's key was checked under other public values (ranges, rows, codes) than this configuration's: key, entry and proof must be checked under one Configured"
    );
    let plans = c.proof();
    let table = tested.reader();
    let name = IndexName { commitment: table.commitment(), record: table.record().clone() };
    let made_on = match read_head_entry(file, HEAD_TAG_PROOF) {
        Ok(n) => n,
        Err(w) => {
            *why = Some(w);
            return ProofVerdict::No;
        }
    };
    if made_on != entry {
        *why = Some("the proof was made on another stored copy of the table");
        return ProofVerdict::No;
    }

    let mut first_b = Binder::new(LABEL_FIRST_CHAIN, plans.chains[0].plan.clone());
    let mut x = bind_request_parameters(&mut first_b, c);
    if let Some(more) = more {
        more(&mut first_b);
    }
    bind_request_statement(&mut first_b, &mut x, &name, entry, request, file_words);
    let mut session = VerifierSession::new();
    let mut first_ch = VerifierRounds::new(&mut first_b, file, &mut session, calls);
    let planned_pending = *first_ch.get(&x.pending_rows);
    let binding_shape = *first_ch.get(&x.binding);
    let first_configuration = *first_ch.configuration();
    let mut first_V = VerifierContext::new(&x.lin.codes, &mut first_ch);
    let mut r = LinksResult::new();
    if !links(&mut first_V, &x, &mut r, calls) {
        drop(first_V);
        return no(&first_ch, why, &mut at, "first chain: the links");
    }
    assert!(
        same_key_values(),
        "check_proof: the caller's routine for the links has changed the configuration under which this proof is being checked"
    );
    assert!(r.replied, "check_proof: the links hand out no reply");
    if r.reply != *reply {
        drop(first_V);
        set_place(&mut at, Some("first chain: the reply"));
        *why = Some("the proof is about another reply");
        return ProofVerdict::No;
    }
    assert!(
        r.pending.len() as u64 == planned_pending,
        "check_proof: the links leave another number of rows on the table than the first query says"
    );
    let mut first = LinFirst::default();
    if !member_first_verify(
        &mut first_V,
        &x.lin,
        r.index_masks,
        core::mem::take(&mut r.pending),
        &mut first,
        calls,
    ) {
        drop(first_V);
        return no(&first_ch, why, &mut at, "first chain: the rows on the table");
    }
    let first_state = take_chain_state(first_V);
    let (good, seal) = first_ch.seal(R_SEAL, calls);
    if !good {
        return no(&first_ch, why, &mut at, "first chain: its end");
    }
    if !first_ch.finish_inside_a_file() {
        return no(&first_ch, why, &mut at, "first chain: its end");
    }
    drop(first_ch);

    set_place(&mut at, Some("between the first chain and the shared chain"));
    let mut binding_root = LinBindingRoot::default();
    let place = {
        // The place's first item, read once more for the caller.
        let mut ahead = file.clone();
        ahead.get_u64().unwrap_or(0)
    };
    if !crate::iop::lin::lin_binding_root(
        file,
        &binding_shape,
        &first_configuration,
        seal.digest(),
        &mut binding_root,
        calls,
    ) {
        *why = Some("the request's place in its batch");
        return ProofVerdict::No;
    }

    let mut shared_b = Binder::new(LABEL_PROOF_SHARED_CHAIN, plans.chains[1].plan.clone());
    let shared_x = bind_shared_chain(&mut shared_b, c, &name, &binding_root);
    let mut shared_ch = VerifierRounds::new(&mut shared_b, file, &mut session, calls);
    let mut shared_V = VerifierContext::new(&shared_x.codes, &mut shared_ch);
    let table_read = TableRead::tested(tested.reader(), tested.tested_under().unwrap());
    let mut shared = LinShared::default();
    if !crate::iop::lin::lin_shared_verify(
        &mut shared_V,
        &shared_x,
        TableTest::Later,
        &table_read,
        &mut shared,
        calls,
    ) {
        drop(shared_V);
        return no(&shared_ch, why, &mut at, "shared chain");
    }
    if !crate::iop::lin::lin_shared_tests_verify(&mut shared_V, &shared_x, &mut shared, calls) {
        drop(shared_V);
        return no(&shared_ch, why, &mut at, "shared chain: a proximity test");
    }
    let shared_state = take_chain_state(shared_V);
    let (good, shared_seal) = shared_ch.seal(R_SEAL, calls);
    if !good {
        return no(&shared_ch, why, &mut at, "shared chain: its end");
    }
    if !shared_ch.finish_inside_a_file() {
        return no(&shared_ch, why, &mut at, "shared chain: its end");
    }
    shared_state.st.require_all_tested();
    drop(shared_ch);

    let mut second_b = Binder::new(LABEL_PROOF_SECOND_CHAIN, plans.chains[2].plan.clone());
    bind_second_chain(&mut second_b, c, &seal, &shared_seal);
    let mut second_ch = VerifierRounds::new(&mut second_b, file, &mut session, calls);
    let mut V = continue_chain(first_state, &mut second_ch, None);
    let mut second = LinSecond::default();
    if !lin_second_verify_with(
        &mut V,
        &x.lin,
        &first,
        &shared_state.st,
        &shared_state.book,
        &shared,
        &mut second,
        calls,
    ) {
        drop(V);
        return no(&second_ch, why, &mut at, "second chain");
    }
    if !crate::iop::lin::lin_second_tests_verify(&mut V, &x.lin, &mut first, &second, calls) {
        drop(V);
        return no(&second_ch, why, &mut at, "second chain: a proximity test");
    }
    let second_state = take_chain_state(V);
    if !second_ch.finish() {
        return no(&second_ch, why, &mut at, "second chain: its end");
    }
    second_state.st.require_all_tested();
    drop(second_ch);
    set_place(&mut at, Some("behind the chains"));
    if !session.accepted() {
        *why = Some("a chain of the proof was refused");
        return ProofVerdict::No;
    }
    if let Some(f) = facts {
        f.seal = *seal.digest();
        f.place = place;
    }
    *why = None;
    set_place(&mut at, None);
    if c.needs_work() {
        ProofVerdict::YesWithWork
    } else {
        ProofVerdict::Yes
    }
}

/// `check_proof_if_tested` (check.h:224-231).
#[allow(clippy::too_many_arguments)]
pub fn check_proof_if_tested(
    c: &Configured,
    table: &UnprovedTable,
    entry: u32,
    request: &[u8],
    file_words: &[u8],
    reply: &E,
    file: &mut Reader<'_>,
    links: &mut LinksCheck<'_>,
    more: Option<&mut MoreParameters<'_>>,
    calls: &mut HashCalls,
    why: &mut Option<&'static str>,
    facts: Option<&mut ProofFacts>,
    at: Option<&mut Option<&'static str>>,
) -> IfTested {
    let mut at = at;
    let tested = table.as_if_tested();
    let verdict =
        check_proof(c, &tested, entry, request, file_words, reply, file, links, more, calls, why, facts, at.as_deref_mut());
    if verdict == ProofVerdict::No {
        return IfTested::No;
    }
    // Never null here, so that "no reason was given" cannot be taken for a yes.
    *why = Some(IF_TESTED_WHY);
    set_place(&mut at, Some(IF_TESTED_WHY));
    match verdict {
        ProofVerdict::Yes => IfTested::YesIfTheTableIsTested,
        ProofVerdict::YesWithWork => IfTested::YesWithWorkIfTheTableIsTested,
        ProofVerdict::No => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    use crate::consts::PROGRAM_VERSION_WORD;
    use crate::frame::configure::{configure, Shapes};
    use crate::frame::files::stand_in_subproofs;
    use crate::frame::hiding_conditions::RangeCheck;
    use crate::frame::parameters::Parameters;
    use crate::iop::foldeq::{IndexKey, IndexRecord};

    const POLICY: &str = include_str!("../../../fixtures/config-standin/policy.txt");

    fn shapes() -> Shapes {
        let mut s = Shapes { sub: stand_in_subproofs(), ..Shapes::default() };
        s.layout.link = vec![Vec::new(); s.sub.request.link.len()];
        s.identifiers = (0..s.sub.request.link.len() as u64).map(|i| 1000 + i).collect();
        s.range_checks.push(RangeCheck {
            rows: 1,
            columns: 1,
            combinations: 1,
            bound: 2,
            range: 1 << 19,
            digit_bits: [10, 10],
        });
        s
    }

    /// The accepted stand-in configuration of `frame_configure_vectors.rs`.
    fn configured() -> Configured {
        let files: [&[u8]; 1] = [POLICY.as_bytes()];
        let c = configure(&files, &|_: &[&[u8]], _: &Parameters| shapes());
        assert!(c.refused().is_empty(), "the stand-in policy must be accepted: {}", c.refused());
        c
    }

    /// A table that counts as tested under `c`, with the key's public bytes.
    fn tested_table(c: &Configured) -> TestedTable {
        let fixed = key_fixed(c.sized(), c.configuration());
        let shape = fixed.lin.fold.index.clone();
        let answers = (shape.rows() * shape.answers as u64) as usize;
        let key = IndexKey::new(
            shape,
            c.configuration(),
            &Digest::zero(),
            IndexRecord { y: vec![E::zero(); answers] },
        );
        TestedTable::new_tested(key, &c.sized().d.set, key_public_bytes(&fixed))
    }

    fn links_accept(
        _: &mut VerifierContext<'_, '_, '_, '_>,
        _: &RequestPublic,
        _: &mut LinksResult,
        _: &mut HashCalls,
    ) -> bool {
        true
    }

    fn links_reject(
        _: &mut VerifierContext<'_, '_, '_, '_>,
        _: &RequestPublic,
        _: &mut LinksResult,
        _: &mut HashCalls,
    ) -> bool {
        false
    }

    #[test]
    fn a_refused_configuration_is_no_before_the_chains() {
        let c = configure(&[], &|_: &[&[u8]], _: &Parameters| Shapes::default());
        let tested = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut at = None;
        let mut facts = ProofFacts::default();
        let mut calls = HashCalls::default();
        let more: Option<&mut MoreParameters<'_>> = None;
        let verdict = check_proof(
            &c,
            &tested,
            0,
            &[],
            &[],
            &E::zero(),
            &mut file,
            &mut links_accept,
            more,
            &mut calls,
            &mut why,
            Some(&mut facts),
            Some(&mut at),
        );
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some("the public files are not admitted"));
        assert_eq!(at, Some("before the chains"));
        assert_eq!(facts.seal, Digest::zero());
    }

    #[test]
    fn an_untested_table_is_no_before_the_chains() {
        let c = configured();
        let tested = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut at = None;
        let mut calls = HashCalls::default();
        let more: Option<&mut MoreParameters<'_>> = None;
        let verdict = check_proof(
            &c,
            &tested,
            0,
            &[],
            &[],
            &E::zero(),
            &mut file,
            &mut links_accept,
            more,
            &mut calls,
            &mut why,
            None,
            Some(&mut at),
        );
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(
            why,
            Some("the table has passed no check: its key or entry was refused, or was never checked")
        );
        assert_eq!(at, Some("before the chains"));
    }

    fn proof_header(tag: u32, version: u32) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(&tag.to_le_bytes());
        v.extend_from_slice(&version.to_le_bytes());
        v.extend_from_slice(&0u32.to_le_bytes());
        v
    }

    fn check_a_proof_file(bytes: &[u8]) -> (ProofVerdict, Option<&'static str>, Option<&'static str>) {
        let c = configured();
        let tested = tested_table(&c);
        let mut file = Reader::new(bytes);
        let mut why = None;
        let mut at = None;
        let mut calls = HashCalls::default();
        let more: Option<&mut MoreParameters<'_>> = None;
        let verdict = check_proof(
            &c,
            &tested,
            0,
            &[],
            &[],
            &E::zero(),
            &mut file,
            &mut links_accept,
            more,
            &mut calls,
            &mut why,
            None,
            Some(&mut at),
        );
        (verdict, why, at)
    }

    #[test]
    fn a_short_proof_header_is_a_rejection_before_any_chain() {
        let (verdict, why, at) = check_a_proof_file(&[]);
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some("file-too-short"));
        assert_eq!(at, Some("before the chains"));
    }

    #[test]
    fn a_proof_file_of_another_kind_is_a_rejection_before_any_chain() {
        let bytes = proof_header(0x4b495043, PROGRAM_VERSION_WORD); // "CPIK": a key file's tag
        let (verdict, why, at) = check_a_proof_file(&bytes);
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some("file-of-another-kind"));
        assert_eq!(at, Some("before the chains"));
    }

    #[test]
    fn a_proof_file_of_another_version_is_a_rejection_before_any_chain() {
        let bytes = proof_header(0x46505043, PROGRAM_VERSION_WORD ^ 1); // "CPPF"
        let (verdict, why, at) = check_a_proof_file(&bytes);
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some("version-unknown"));
        assert_eq!(at, Some("before the chains"));
    }

    #[test]
    fn a_proof_without_its_first_salt_is_no_at_the_links() {
        // The header is complete, so the first chain is built; its salt is missing, so every read
        // fails and the caller's callback sees the rejection.
        let bytes = proof_header(0x46505043, PROGRAM_VERSION_WORD);
        let c = configured();
        let tested = tested_table(&c);
        let mut file = Reader::new(&bytes);
        let mut why = None;
        let mut at = None;
        let mut calls = HashCalls::default();
        let more: Option<&mut MoreParameters<'_>> = None;
        let verdict = check_proof(
            &c,
            &tested,
            0,
            &[],
            &[],
            &E::zero(),
            &mut file,
            &mut links_reject,
            more,
            &mut calls,
            &mut why,
            None,
            Some(&mut at),
        );
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some("the chain's salt is missing"));
        assert_eq!(at, Some("first chain: the links"));
    }

    #[test]
    fn a_proof_made_on_another_stored_copy_is_a_rejection() {
        let mut bytes = proof_header(0x46505043, PROGRAM_VERSION_WORD);
        bytes[8] = 1; // the file's entry number is 1, the check's is 0
        let (verdict, why, _) = check_a_proof_file(&bytes);
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some("the proof was made on another stored copy of the table"));
    }

    #[test]
    #[should_panic(expected = "check_proof: the table's key was checked under other public values")]
    fn a_table_checked_under_other_public_values_ends_the_process() {
        let c = configured();
        let tested = TestedTable::new_tested(
            IndexKey::default(),
            &c.sized().d.set,
            alloc::vec![1u8, 2, 3],
        );
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut calls = HashCalls::default();
        let more: Option<&mut MoreParameters<'_>> = None;
        check_proof(
            &c,
            &tested,
            0,
            &[],
            &[],
            &E::zero(),
            &mut file,
            &mut links_accept,
            more,
            &mut calls,
            &mut why,
            None,
            None,
        );
    }

    #[test]
    fn if_tested_is_no_for_an_unread_table() {
        let c = configured();
        let table = UnprovedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut calls = HashCalls::default();
        let more: Option<&mut MoreParameters<'_>> = None;
        let verdict = check_proof_if_tested(
            &c,
            &table,
            0,
            &[],
            &[],
            &E::zero(),
            &mut file,
            &mut links_accept,
            more,
            &mut calls,
            &mut why,
            None,
            None,
        );
        assert_eq!(verdict, IfTested::No);
    }

    #[test]
    fn if_tested_keeps_no_for_a_rejection_in_the_file() {
        let c = configured();
        let fixed = key_fixed(c.sized(), c.configuration());
        let shape = fixed.lin.fold.index.clone();
        let key = IndexKey::new(
            shape.clone(),
            c.configuration(),
            &Digest::zero(),
            IndexRecord { y: vec![E::zero(); (shape.rows() * shape.answers as u64) as usize] },
        );
        let table = UnprovedTable::new_read(key, &c.sized().d.set, key_public_bytes(&fixed));
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut calls = HashCalls::default();
        let more: Option<&mut MoreParameters<'_>> = None;
        let verdict = check_proof_if_tested(
            &c,
            &table,
            0,
            &[],
            &[],
            &E::zero(),
            &mut file,
            &mut links_accept,
            more,
            &mut calls,
            &mut why,
            None,
            None,
        );
        assert_eq!(verdict, IfTested::No);
        assert_eq!(why, Some("file-too-short"));
    }
}
