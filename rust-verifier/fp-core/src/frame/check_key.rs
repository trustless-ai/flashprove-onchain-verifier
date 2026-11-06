//! The verifier's check of a key file, ported from `blocks/frame/check_key.h`.
//!
//! A key file asserts two things about the committed table under its Merkle root: its matrix
//! entries are in their ranges (WF) and the table is within the one-time distance of one codeword
//! (LIN, a batch of one). `check_key` runs the three chains of a key file and leaves a
//! `TestedTable` for the later proofs that read the table.
//!
//! Ported: `KeyPublic`, `bind_one_time_chain`, `KeyPlans`, `KeyUnder`, `key_under`,
//! `read_key_table_unproved` (both overloads), `check_key_under` and `check_key`. `make_key*` and
//! the test-only constructors are not ported.
//!
//! Deviations at the verifier's boundary: `KeyUnder`'s members are public where C++ keeps them
//! const and private, because Rust has no friend functions; `read_key_table_unproved`'s two C++
//! overloads carry distinct names (`_configured` for the `Configured` one); `why` is an
//! out-parameter (`Option<&'static str>`) as in C++. Reasons from a channel are static, as
//! `VerifierRounds::why` returns. The second chain's context is rebuilt around the first chain's
//! `Statement` and `TreeBook` (`check::continue_chain`), and `lin_second_verify`'s check that the
//! second chain follows the shared one is structural: `lin_bind_second` binds both seals first.

#![allow(non_snake_case)] // the C++ names `V`, `first_V`, `shared_V`

use alloc::rc::Rc;

use crate::chain::public::{Binder, Public};
use crate::chain::rounds::VerifierRounds;
use crate::chain::session::VerifierSession;
use crate::field::ext::E;
use crate::frame::check::{
    continue_chain, does_not_hold, lin_second_verify_with, notes_done, notes_start, set_place,
    take_chain_state, Notes,
};
use crate::frame::configure::{Configured, ProofVerdict};
use crate::frame::heads::{read_head, HEAD_TAG_KEY, LABEL_ONE_TIME_CHAIN};
use crate::frame::key_fixed::{key_fault, key_fixed, key_public_bytes, KeyFixed};
use crate::hash::calls::HashCalls;
use crate::hash::modes::Digest;
use crate::iop::context::{OracleNotice, VerifierContext};
use crate::iop::foldeq::{
    index_key_fault, IndexKey, IndexName, IndexReader, IndexRecord, TableRead, TestedTable,
    UnprovedTable,
};
use crate::iop::lin::{
    lin_bind, lin_bind_second, lin_bind_shared, lin_binding_root, LinBindingRoot,
    LinBindingShape, LinFirst, LinPublic, LinSecond, LinShared, LIN_LABEL_SECOND,
    LIN_LABEL_SHARED,
};
use crate::iop::member::member_first_verify;
use crate::iop::message::Reader;
use crate::iop::send::{send_verify, AnswersRound};
use crate::iop::wf::{wf_verify, WfOutput, WfPublic};
use crate::numbers::plan::{Plan, Planned, TableTest};
use crate::numbers::round_names::R_SEAL;

// ------------------------------------------------------------------------------------------------
// A key file's public values and the run's plans
// ------------------------------------------------------------------------------------------------

/// A key file's public values, as the one-time chain's first query contains them (`KeyPublic`,
/// check_key.h:42-47).
#[derive(Clone, Debug, Default)]
pub struct KeyPublic {
    /// Codes, the shape of the test on the table, the table's root and record.
    pub lin: LinPublic,
    pub index_masks: Public<OracleNotice>,
    pub ranges: Public<WfPublic>,
    pub binding: Public<LinBindingShape>,
}

/// `bind_one_time_chain` (check_key.h:48-56). LIN comes last: its statement item closes the
/// parameters.
pub fn bind_one_time_chain(b: &mut Binder, f: &KeyFixed, table: &IndexName) -> KeyPublic {
    let mut x = KeyPublic::default();
    b.configuration(&f.configuration);
    x.index_masks = b.parameter("index-mask message", f.index_masks.clone());
    x.ranges = b.parameter("ranges", f.ranges.clone());
    x.binding = b.parameter("binding tree", f.binding);
    x.lin = lin_bind(b, &f.codes, &f.lin, table);
    x
}

/// The plans of a key file's three chains (`KeyPlans`, check_key.h:58-60).
#[derive(Clone, Debug, Default)]
pub struct KeyPlans {
    pub one_time: Rc<Planned>,
    pub shared: Rc<Planned>,
    pub second: Rc<Planned>,
}

/// The plans and values of a run (`KeyUnder`, check_key.h:62-73). Only `key_under` makes one.
#[derive(Clone, Debug)]
pub struct KeyUnder {
    pub plans: KeyPlans,
    pub fixed: KeyFixed,
}

/// `key_under` (check_key.h:240-243): plans and values all come from `c`, as copies.
pub fn key_under(c: &Configured) -> KeyUnder {
    assert!(
        c.refused().is_empty() && c.key().chains.len() == 3,
        "a key has three chains"
    );
    KeyUnder {
        plans: KeyPlans {
            one_time: c.key().chains[0].plan.clone(),
            shared: c.key().chains[1].plan.clone(),
            second: c.key().chains[2].plan.clone(),
        },
        fixed: key_fixed(c.sized(), c.configuration()),
    }
}

// ------------------------------------------------------------------------------------------------
// Reading the table's root and record
// ------------------------------------------------------------------------------------------------

/// `read_key_table_unproved` (check_key.h:153-164): header | root | the record's answers, without
/// the file's proofs. Only the form is checked: tag, version word, canonical elements,
/// `index_key_fault`.
pub fn read_key_table_unproved(
    fixed: &KeyFixed,
    file: &mut Reader<'_>,
    table: &mut IndexKey,
) -> Result<(), &'static str> {
    if let Some(why) = read_head(file, HEAD_TAG_KEY) {
        return Err(why);
    }
    let shape = &fixed.lin.fold.index;
    let mut read = IndexKey::new(
        shape.clone(),
        &fixed.configuration,
        &Digest::zero(),
        IndexRecord::default(),
    );
    match file.get_digest() {
        Some(root) => read.root = root,
        None => return Err("the table's root"),
    }
    read.rec.y = alloc::vec![E::zero(); (shape.rows() * shape.answers as u64) as usize];
    for y in &mut read.rec.y {
        match file.get_e() {
            Some(v) => *y = v,
            None => return Err("the record's answers"),
        }
    }
    if let Some(why) = index_key_fault(&read) {
        return Err(why);
    }
    *table = read;
    Ok(())
}

/// `read_key_table_unproved` under a `Configured` (check_key.h:258-264). No proof is checked; the
/// result's type, `UnprovedTable`, limits what it can be used for.
pub fn read_key_table_unproved_configured(
    c: &Configured,
    file: &mut Reader<'_>,
    table: &mut UnprovedTable,
) -> Result<(), &'static str> {
    if !c.refused().is_empty() {
        return Err("the public files are not admitted");
    }
    let fixed = key_fixed(c.sized(), c.configuration());
    let mut read = IndexKey::default();
    read_key_table_unproved(&fixed, file, &mut read)?;
    *table = UnprovedTable::new_read(read, &c.sized().d.set, key_public_bytes(&fixed));
    Ok(())
}

// ------------------------------------------------------------------------------------------------
// The check
// ------------------------------------------------------------------------------------------------

/// A rejection's `why` and `place` for `check_key_under` (`no`, check_key.h:174-177).
fn no(
    ch: &VerifierRounds<'_, '_, '_>,
    why: &mut Option<&'static str>,
    place: &mut Option<&mut Option<&'static str>>,
    where_: &'static str,
) -> bool {
    set_place(place, Some(where_));
    *why = Some(ch.why().unwrap_or(where_));
    false
}

/// `check_key_under` (check_key.h:170-235). True: `key` is what a verifier keeps of the table for
/// later proofs, with the `Setting` under which this test passed.
#[allow(clippy::too_many_arguments)]
pub fn check_key_under(
    under: &KeyUnder,
    file: &mut Reader<'_>,
    key: &mut TestedTable,
    calls: &mut HashCalls,
    why: &mut Option<&'static str>,
    mut notes: Option<&mut Notes>,
    place: Option<&mut Option<&'static str>>,
) -> bool {
    let mut place = place;
    let plans = &under.plans;
    let fixed = &under.fixed;
    set_place(&mut place, Some("before the chains"));
    if let Some(w) = key_fault(fixed) {
        *why = Some(w);
        return false;
    }
    for p in [&plans.one_time, &plans.shared, &plans.second] {
        if !p.holds() {
            // No key is worth anything under such parameters.
            *why = Some(does_not_hold(p, "check_key"));
            return false;
        }
    }
    assert!(
        Plan::same_setting(&plans.one_time.set, &plans.shared.set)
            && Plan::same_setting(&plans.shared.set, &plans.second.set),
        "check_key: a key's three chains are planned under one setting"
    );
    let mut read = IndexKey::default();
    if let Err(w) = read_key_table_unproved(fixed, file, &mut read) {
        *why = Some(w);
        return false;
    }
    let name = IndexName { commitment: read.commitment(), record: read.rec.clone() };

    let mut first_b = Binder::new(LABEL_ONE_TIME_CHAIN, plans.one_time.clone());
    let x = bind_one_time_chain(&mut first_b, fixed, &name);
    let mut session = VerifierSession::new();
    let mut first_ch = VerifierRounds::new(&mut first_b, file, &mut session, calls);
    let index_masks = first_ch.get(&x.index_masks).clone();
    let binding_shape = *first_ch.get(&x.binding);
    let first_configuration = *first_ch.configuration();
    let mut first_V = VerifierContext::new(&x.lin.codes, &mut first_ch);
    first_V.notes = notes_start(notes.as_deref_mut());
    let (good, ids) = send_verify(&mut first_V, &[index_masks], AnswersRound::Own, calls);
    if !good {
        notes_done(notes.as_deref_mut(), &mut first_V.notes);
        drop(first_V);
        return no(&first_ch, why, &mut place, "one-time chain: the index-mask message");
    }
    let mut left = WfOutput::default();
    if !wf_verify(&mut first_V, &x.ranges, &x.lin, ids[0], &mut left, calls) {
        notes_done(notes.as_deref_mut(), &mut first_V.notes);
        drop(first_V);
        return no(&first_ch, why, &mut place, "one-time chain: the ranges");
    }
    let mut first = LinFirst::default();
    if !member_first_verify(
        &mut first_V,
        &x.lin,
        ids[0],
        left.pending.take(),
        &mut first,
        calls,
    ) {
        notes_done(notes.as_deref_mut(), &mut first_V.notes);
        drop(first_V);
        return no(&first_ch, why, &mut place, "one-time chain: the rows on the table");
    }
    notes_done(notes.as_deref_mut(), &mut first_V.notes);
    let first_state = take_chain_state(first_V);
    let (good, seal) = first_ch.seal(R_SEAL, calls);
    if !good || !first_ch.finish_inside_a_file() {
        return no(&first_ch, why, &mut place, "one-time chain: its end");
    }
    drop(first_ch);

    let mut binding_root = LinBindingRoot::default();
    set_place(&mut place, Some("between the one-time chain and the shared chain"));
    if !lin_binding_root(
        file,
        &binding_shape,
        &first_configuration,
        seal.digest(),
        &mut binding_root,
        calls,
    ) {
        *why = Some("the seal's place");
        return false;
    }

    let mut shared_b = Binder::new(LIN_LABEL_SHARED, plans.shared.clone());
    shared_b.configuration(&fixed.configuration);
    let shared_x = lin_bind_shared(&mut shared_b, &fixed.codes, &fixed.lin, &name, &binding_root);
    let mut shared_ch = VerifierRounds::new(&mut shared_b, file, &mut session, calls);
    let mut shared_V = VerifierContext::new(&shared_x.codes, &mut shared_ch);
    shared_V.notes = notes_start(notes.as_deref_mut());
    let mut shared = LinShared::default();
    let table = TableRead::untested(&read);
    if !crate::iop::lin::lin_shared_verify(
        &mut shared_V,
        &shared_x,
        TableTest::OneTime,
        &table,
        &mut shared,
        calls,
    ) {
        notes_done(notes.as_deref_mut(), &mut shared_V.notes);
        drop(shared_V);
        return no(&shared_ch, why, &mut place, "shared chain");
    }
    if !crate::iop::lin::lin_shared_tests_verify(&mut shared_V, &shared_x, &mut shared, calls)
    {
        notes_done(notes.as_deref_mut(), &mut shared_V.notes);
        drop(shared_V);
        return no(&shared_ch, why, &mut place, "shared chain: a proximity test");
    }
    notes_done(notes.as_deref_mut(), &mut shared_V.notes);
    let shared_state = take_chain_state(shared_V);
    let (good, shared_seal) = shared_ch.seal(R_SEAL, calls);
    if !good || !shared_ch.finish_inside_a_file() {
        return no(&shared_ch, why, &mut place, "shared chain: its end");
    }
    shared_state.st.require_all_tested();
    drop(shared_ch);

    let mut second_b = Binder::new(LIN_LABEL_SECOND, plans.second.clone());
    second_b.configuration(&fixed.configuration);
    lin_bind_second(&mut second_b, &seal, &shared_seal);
    let mut second_ch = VerifierRounds::new(&mut second_b, file, &mut session, calls);
    let mut V = continue_chain(first_state, &mut second_ch, notes.as_deref_mut());
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
        notes_done(notes.as_deref_mut(), &mut V.notes);
        drop(V);
        return no(&second_ch, why, &mut place, "second chain");
    }
    if !crate::iop::lin::lin_second_tests_verify(&mut V, &x.lin, &mut first, &second, calls) {
        notes_done(notes.as_deref_mut(), &mut V.notes);
        drop(V);
        return no(&second_ch, why, &mut place, "second chain: a proximity test");
    }
    notes_done(notes.as_deref_mut(), &mut V.notes);
    let second_state = take_chain_state(V);
    if !second_ch.finish() {
        return no(&second_ch, why, &mut place, "second chain: its end");
    }
    second_state.st.require_all_tested();
    drop(second_ch);
    set_place(&mut place, Some("behind the chains"));
    if !session.accepted() {
        // The verdict: false if a chain rejected, even if a result above was dropped.
        *why = Some("a chain of the key has refused");
        return false;
    }
    set_place(&mut place, None);
    *key = TestedTable::new_tested(read, &plans.shared.set, key_public_bytes(fixed));
    *why = None;
    true
}

/// `check_key` (check_key.h:276-281). `NO` leaves `key` unchanged.
#[allow(clippy::too_many_arguments)]
pub fn check_key(
    c: &Configured,
    file: &mut Reader<'_>,
    key: &mut TestedTable,
    calls: &mut HashCalls,
    why: &mut Option<&'static str>,
    notes: Option<&mut Notes>,
    place: Option<&mut Option<&'static str>>,
) -> ProofVerdict {
    let mut place = place;
    set_place(&mut place, Some("before the chains"));
    if !c.refused().is_empty() {
        *why = Some("the public files are not admitted");
        return ProofVerdict::No;
    }
    if !check_key_under(&key_under(c), file, key, calls, why, notes, place) {
        return ProofVerdict::No;
    }
    if c.work_of_the_key().needed {
        ProofVerdict::YesWithWork
    } else {
        ProofVerdict::Yes
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use crate::consts::PROGRAM_VERSION_WORD;
    use crate::frame::check::DOES_NOT_HOLD_WHY;
    use crate::frame::configure::{configure, Shapes};
    use crate::frame::files::{refused_file, stand_in_subproofs, FilePlan, Sized};
    use crate::frame::heads::HEAD_TAG_PROOF;
    use crate::frame::hiding_conditions::RangeCheck;
    use crate::frame::parameters::Parameters;
    use crate::iop::foldeq::IndexKey;
    use crate::iop::message::Reader;

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

    fn configured() -> Configured {
        let files: [&[u8]; 1] = [POLICY.as_bytes()];
        let c = configure(&files, &|_: &[&[u8]], _: &Parameters| shapes());
        assert!(c.refused().is_empty(), "the stand-in policy must be accepted: {}", c.refused());
        c
    }

    fn header(tag: u32, version: u32) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(&tag.to_le_bytes());
        v.extend_from_slice(&version.to_le_bytes());
        v
    }

    fn record_bytes(fixed: &KeyFixed) -> usize {
        let shape = &fixed.lin.fold.index;
        (shape.rows() * shape.answers as u64) as usize * 24
    }

    /// A well-formed key file's table part: header, a zero root, zero answers.
    fn good_table(fixed: &KeyFixed) -> Vec<u8> {
        let mut v = header(HEAD_TAG_KEY, PROGRAM_VERSION_WORD);
        v.extend_from_slice(&[0u8; 32]);
        v.resize(v.len() + record_bytes(fixed), 0);
        v
    }

    #[test]
    fn a_short_header_refuses_the_table() {
        let c = configured();
        let fixed = key_fixed(c.sized(), c.configuration());
        let mut key = IndexKey::default();
        let mut file = Reader::new(&[]);
        assert_eq!(
            read_key_table_unproved(&fixed, &mut file, &mut key),
            Err("file-too-short")
        );
        assert!(key.table.code.log_n == 0); // unchanged
    }

    #[test]
    fn a_wrong_tag_refuses_the_table() {
        let c = configured();
        let fixed = key_fixed(c.sized(), c.configuration());
        let mut key = IndexKey::default();
        let bytes = header(HEAD_TAG_PROOF, PROGRAM_VERSION_WORD);
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_key_table_unproved(&fixed, &mut file, &mut key),
            Err("file-of-another-kind")
        );
    }

    #[test]
    fn a_wrong_version_refuses_the_table() {
        let c = configured();
        let fixed = key_fixed(c.sized(), c.configuration());
        let mut key = IndexKey::default();
        let bytes = header(HEAD_TAG_KEY, PROGRAM_VERSION_WORD ^ 1);
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_key_table_unproved(&fixed, &mut file, &mut key),
            Err("version-unknown")
        );
    }

    #[test]
    fn a_missing_root_refuses_the_table() {
        let c = configured();
        let fixed = key_fixed(c.sized(), c.configuration());
        let mut key = IndexKey::default();
        let bytes = header(HEAD_TAG_KEY, PROGRAM_VERSION_WORD);
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_key_table_unproved(&fixed, &mut file, &mut key),
            Err("the table's root")
        );
    }

    #[test]
    fn a_short_record_refuses_the_table() {
        let c = configured();
        let fixed = key_fixed(c.sized(), c.configuration());
        let mut key = IndexKey::default();
        let mut bytes = header(HEAD_TAG_KEY, PROGRAM_VERSION_WORD);
        bytes.extend_from_slice(&[0u8; 32]);
        bytes.extend_from_slice(&[0u8; 23]);
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_key_table_unproved(&fixed, &mut file, &mut key),
            Err("the record's answers")
        );
    }

    #[test]
    fn a_non_canonical_answer_refuses_the_table() {
        let c = configured();
        let fixed = key_fixed(c.sized(), c.configuration());
        let mut key = IndexKey::default();
        let mut bytes = header(HEAD_TAG_KEY, PROGRAM_VERSION_WORD);
        bytes.extend_from_slice(&[0u8; 32]);
        bytes.extend_from_slice(&[0xffu8; 24]);
        bytes.resize(bytes.len() + record_bytes(&fixed) - 24, 0);
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_key_table_unproved(&fixed, &mut file, &mut key),
            Err("the record's answers")
        );
    }

    #[test]
    fn a_key_without_a_configuration_digest_is_refused() {
        let c = configured();
        let mut fixed = key_fixed(c.sized(), c.configuration());
        fixed.configuration = Digest::zero();
        let bytes = good_table(&fixed);
        let mut key = IndexKey::default();
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_key_table_unproved(&fixed, &mut file, &mut key),
            Err("the key names no configuration")
        );
    }

    #[test]
    fn a_good_table_is_read_and_the_file_stops_after_it() {
        let c = configured();
        let fixed = key_fixed(c.sized(), c.configuration());
        let mut bytes = good_table(&fixed);
        bytes.push(0xab); // the first proof byte stays unread
        let mut key = IndexKey::default();
        let mut file = Reader::new(&bytes);
        assert_eq!(read_key_table_unproved(&fixed, &mut file, &mut key), Ok(()));
        assert_eq!(key.made_under, *c.configuration());
        assert_eq!(key.root, Digest::zero());
        assert_eq!(key.table, fixed.lin.fold.index);
        assert_eq!(key.rec.y.len(), (key.table.rows() * key.table.answers as u64) as usize);
        assert!(!file.at_end());
        assert_eq!(file.take(1), Some(&[0xab][..]));
        assert!(file.at_end());
    }

    #[test]
    fn the_configured_read_refuses_a_refused_configuration() {
        let c = configure(&[], &|_: &[&[u8]], _: &Parameters| Shapes::default());
        let mut table = UnprovedTable::default();
        let mut file = Reader::new(&[]);
        assert_eq!(
            read_key_table_unproved_configured(&c, &mut file, &mut table),
            Err("the public files are not admitted")
        );
    }

    #[test]
    fn the_configured_read_fills_an_unproved_table() {
        let c = configured();
        let fixed = key_fixed(c.sized(), c.configuration());
        let bytes = good_table(&fixed);
        let mut table = UnprovedTable::default();
        let mut file = Reader::new(&bytes);
        assert_eq!(read_key_table_unproved_configured(&c, &mut file, &mut table), Ok(()));
        assert_eq!(table.reader().made_under, *c.configuration());
        assert!(file.at_end());
    }

    #[test]
    fn check_key_is_no_for_a_refused_configuration() {
        let c = configure(&[], &|_: &[&[u8]], _: &Parameters| Shapes::default());
        let mut key = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let verdict = check_key(&c, &mut file, &mut key, &mut calls, &mut why, None, Some(&mut place));
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some("the public files are not admitted"));
        assert_eq!(place, Some("before the chains"));
        assert!(key.tested_under().is_none());
    }

    #[test]
    fn check_key_is_no_for_a_short_file_before_a_chain() {
        let c = configured();
        let mut key = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let verdict = check_key(&c, &mut file, &mut key, &mut calls, &mut why, None, Some(&mut place));
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some("file-too-short"));
        assert_eq!(place, Some("before the chains"));
        assert!(key.tested_under().is_none());
    }

    #[test]
    fn a_key_file_without_its_first_salt_is_no_in_the_one_time_chain() {
        // The table part is well formed, so the chain is built; its salt is missing, so the
        // index-mask message cannot be received.
        let c = configured();
        let fixed = key_fixed(c.sized(), c.configuration());
        let bytes = good_table(&fixed);
        let mut key = TestedTable::default();
        let mut file = Reader::new(&bytes);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let verdict = check_key(&c, &mut file, &mut key, &mut calls, &mut why, None, Some(&mut place));
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some("the chain's salt is missing"));
        assert_eq!(place, Some("one-time chain: the index-mask message"));
        assert!(key.tested_under().is_none());
    }

    #[test]
    fn a_key_fault_is_the_reason_before_the_chains() {
        let c = configured();
        let mut under = key_under(&c);
        under.fixed.lin.matrix_rows = 0;
        let fault = key_fault(&under.fixed);
        assert!(fault.is_some());
        let mut key = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let good = check_key_under(&under, &mut file, &mut key, &mut calls, &mut why, None, Some(&mut place));
        assert!(!good);
        assert_eq!(why, fault);
        assert_eq!(place, Some("before the chains"));
    }

    #[test]
    fn plans_that_do_not_hold_are_the_reason_before_the_chains() {
        let c = configured();
        let mut f = FilePlan::default();
        let z = Sized { refused: String::from("made up"), ..Sized::default() };
        assert!(refused_file(&mut f, &z, &["one-time chain", "shared chain", "second chain"]));
        let under = KeyUnder {
            plans: KeyPlans {
                one_time: f.chains[0].plan.clone(),
                shared: f.chains[1].plan.clone(),
                second: f.chains[2].plan.clone(),
            },
            fixed: key_fixed(c.sized(), c.configuration()),
        };
        assert_eq!(under.plans.one_time.why_not(), "made up");
        let mut key = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let good = check_key_under(&under, &mut file, &mut key, &mut calls, &mut why, None, Some(&mut place));
        assert!(!good);
        assert_eq!(why, Some(DOES_NOT_HOLD_WHY));
        // The cause itself stays on the plan, where a caller can read it.
        assert_eq!(under.plans.one_time.why_not(), "made up");
        assert_eq!(place, Some("before the chains"));
    }
}
