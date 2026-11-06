//! The verifier's check of a leaf file (`entry` in identifiers), ported from
//! `blocks/frame/check_entry.h`.
//!
//! A leaf file holds a leaf table's root, its record and a LINK proof that ties the table to an
//! anchor's table. `check_entry` accepts the file under one `Configured` and leaves a
//! `TestedTable` for every proof made against it; `check_entry_if_tested` is the split-process form
//! for a caller whose key file was checked elsewhere.
//!
//! Ported: `EntryFixed`, `entry_fixed` (both C++ overloads, the `Configured` one as `entry_fixed`
//! and the parts one as `entry_fixed_of`), `entry_fault`, `EntryUnder`, `entry_under`,
//! `read_entry_table_unproved` (both overloads, the `Configured` one as
//! `read_entry_table_unproved_configured`), `check_entry_under`, `check_entry` and
//! `check_entry_if_tested`. `make_entry*` is not ported.
//!
//! Deviations at the verifier's boundary: `why` is `Option<String>` because `link_verify` builds
//! its reason as text where the key and proof checks use fixed strings; `Notes` is the port's
//! alias for C++'s `std::vector<std::pair<std::string, E>>`. `link_verify` in `iop/link.rs` takes
//! the notes vector by value and does not return it, so the values that LINK records do not reach
//! the caller's vector; the parameter is still handed in, as in C++, and the loss is reported.

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;

use crate::chain::session::VerifierSession;
use crate::field::ext::E;
use crate::frame::check::{does_not_hold, notes_start, set_place, Notes};
use crate::frame::configure::{Configured, ProofVerdict};
use crate::frame::heads::{read_head, HEAD_TAG_ENTRY};
use crate::frame::key_fixed::{key_fixed, key_public_bytes};
use crate::frame::link_frame::LinkSized;
use crate::hash::calls::HashCalls;
use crate::hash::modes::Digest;
use crate::iop::foldeq::{
    index_key_fault, IfTested, IndexKey, IndexRecord, TableRead, TestedTable, UnprovedTable,
    IF_TESTED_WHY,
};
use crate::iop::link::{link_fault, link_verify, LinkShape, LinkWhy};
use crate::iop::message::Reader;
use crate::iop::relation::Codes;
use crate::numbers::plan::Planned;

/// The parts of a leaf file that are fixed before a leaf table is committed (`EntryFixed`,
/// check_entry.h:38-42). `link`: the tables' shape, each table's count of drawn columns, the
/// proximity test's stages.
#[derive(Clone, Debug, Default)]
pub struct EntryFixed {
    pub configuration: Digest,
    pub codes: Codes,
    pub link: LinkShape,
}

/// `entry_fixed` (check_entry.h:45-49): `entry_codes`, `link`: as `link_sized()` fills them.
pub fn entry_fixed_of(
    configuration: &Digest,
    entry_codes: &Codes,
    link: &LinkSized,
) -> EntryFixed {
    EntryFixed {
        configuration: *configuration,
        codes: entry_codes.clone(),
        link: link.s.clone(),
    }
}

/// `entry_fixed(const Configured&)` (check_entry.h:196).
pub fn entry_fixed(c: &Configured) -> EntryFixed {
    entry_fixed_of(c.configuration(), &c.sized().entry_codes, &c.sized().link)
}

/// `entry_fault` (check_entry.h:54): null, or what is wrong with the configuration. `plan`: the
/// chain's rounds with their error bounds.
pub fn entry_fault(plan: &Planned, f: &EntryFixed) -> Option<&'static str> {
    link_fault(&f.codes, &f.link, plan.set.samples)
}

/// A plan with the values that it was made for (`EntryUnder`, check_entry.h:72-84). Only
/// `entry_under` constructs it here.
#[derive(Clone, Debug)]
pub struct EntryUnder {
    pub plan: Rc<Planned>,
    pub fixed: EntryFixed,
    /// A `KeyFixed` as bytes, without the table's test distances. The anchor's key file must have
    /// been checked under the same bytes. Empty: a table made by a test constructor, not compared.
    pub key_public: Vec<u8>,
}

/// `entry_under` (check_entry.h:197-200): plan and values are both from `c`.
pub fn entry_under(c: &Configured) -> EntryUnder {
    assert!(
        c.refused().is_empty() && c.entry().chains.len() == 1,
        "an entry has one chain"
    );
    EntryUnder {
        plan: c.entry().chains[0].plan.clone(),
        fixed: entry_fixed(c),
        key_public: key_public_bytes(&key_fixed(c.sized(), c.configuration())),
    }
}

// ------------------------------------------------------------------------------------------------
// Reading the leaf table's root and record
// ------------------------------------------------------------------------------------------------

/// `read_entry_table_unproved` (check_entry.h:130-141): header | the copy's root | the record's
/// answers. The LINK proof is not read; `file` stops at its first byte.
pub fn read_entry_table_unproved(
    fixed: &EntryFixed,
    file: &mut Reader<'_>,
    entry: &mut IndexKey,
) -> Result<(), &'static str> {
    if let Some(why) = read_head(file, HEAD_TAG_ENTRY) {
        return Err(why);
    }
    let shape = &fixed.link.table;
    let mut read = IndexKey::new(
        shape.clone(),
        &fixed.configuration,
        &Digest::zero(),
        IndexRecord::default(),
    );
    match file.get_digest() {
        Some(root) => read.root = root,
        None => return Err("the copy's root"),
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
    *entry = read;
    Ok(())
}

/// `read_entry_table_unproved(const Configured&, ...)` (check_entry.h:205-211).
pub fn read_entry_table_unproved_configured(
    c: &Configured,
    file: &mut Reader<'_>,
    entry: &mut UnprovedTable,
) -> Result<(), &'static str> {
    if !c.refused().is_empty() {
        return Err("the public files are not admitted");
    }
    let fixed = entry_fixed(c);
    let mut read = IndexKey::default();
    read_entry_table_unproved(&fixed, file, &mut read)?;
    *entry =
        UnprovedTable::new_read(read, &c.sized().d.set, key_public_bytes(&key_fixed(c.sized(), c.configuration())));
    Ok(())
}

// ------------------------------------------------------------------------------------------------
// The check
// ------------------------------------------------------------------------------------------------

/// `ENTRY_PLACE_PARAMETERS` and `ENTRY_PLACE_TABLE` (check_entry.h:160).
pub const ENTRY_PLACE_PARAMETERS: &str = "the parameters";
pub const ENTRY_PLACE_TABLE: &str = "head, root and answers";

/// `check_entry_under` (check_entry.h:161-185). `first`: the anchor, from `check_key` on an
/// accepted key file, or from the split-process read of the same bytes.
#[allow(clippy::too_many_arguments)]
pub fn check_entry_under(
    under: &EntryUnder,
    first: &TestedTable,
    file: &mut Reader<'_>,
    entry: &mut TestedTable,
    calls: &mut HashCalls,
    why: &mut Option<String>,
    notes: Option<&mut Notes>,
    place: Option<&mut Option<&'static str>>,
) -> bool {
    let mut place = place;
    set_place(&mut place, Some(ENTRY_PLACE_PARAMETERS));
    if let Some(w) = entry_fault(&under.plan, &under.fixed) {
        *why = Some(String::from(w));
        return false;
    }
    if !under.plan.holds() {
        // No leaf file is worth anything under such parameters.
        *why = Some(String::from(does_not_hold(&under.plan, "check_entry")));
        return false;
    }
    // A rejection, not an abort: this is the case after `check_key` returned NO, for example,
    // which can depend on a key file's bytes.
    if first.tested_under().is_none() {
        *why = Some(String::from(
            "the first table has passed no check: its key was refused, or was never checked",
        ));
        return false;
    }
    assert!(
        under.key_public.is_empty() || first.key_public() == under.key_public.as_slice(),
        "check_entry: the first table's key was checked under other public values (ranges, rows, codes) than this configuration's: key, entry and proof must be checked under one Configured"
    );
    set_place(&mut place, Some(ENTRY_PLACE_TABLE));
    let mut read = IndexKey::default();
    if let Err(w) = read_entry_table_unproved(&under.fixed, file, &mut read) {
        *why = Some(String::from(w));
        return false;
    }
    // One session for each verdict; a leaf file's check is one verdict.
    let mut session = VerifierSession::new();
    let mut said = LinkWhy::default();
    let table = TableRead::tested(first.reader(), first.tested_under().unwrap());
    // `link_verify` also checks that no byte is left over.
    let good = link_verify(
        under.plan.clone(),
        &under.fixed.configuration,
        &under.fixed.codes,
        &under.fixed.link,
        table,
        &read,
        file,
        &mut session,
        Some(&mut said),
        notes_start(notes),
        calls,
    );
    if !good {
        set_place(&mut place, Some(said.step));
        *why = Some(said.reason);
        return false;
    }
    set_place(&mut place, Some(""));
    *entry = TestedTable::new_tested(read, &under.plan.set, first.key_public().to_vec());
    *why = None;
    true
}

/// `check_entry` (check_entry.h:212-218). `NO` leaves `entry` unchanged.
#[allow(clippy::too_many_arguments)]
pub fn check_entry(
    c: &Configured,
    first: &TestedTable,
    file: &mut Reader<'_>,
    entry: &mut TestedTable,
    calls: &mut HashCalls,
    why: &mut Option<String>,
    notes: Option<&mut Notes>,
    place: Option<&mut Option<&'static str>>,
) -> ProofVerdict {
    let mut place = place;
    set_place(&mut place, Some(ENTRY_PLACE_PARAMETERS));
    if !c.refused().is_empty() {
        *why = Some(String::from("the public files are not admitted"));
        return ProofVerdict::No;
    }
    if !check_entry_under(&entry_under(c), first, file, entry, calls, why, notes, place) {
        return ProofVerdict::No;
    }
    if c.work_of_an_entry().needed {
        ProofVerdict::YesWithWork
    } else {
        ProofVerdict::Yes
    }
}

/// `check_entry_if_tested` (check_entry.h:225-232). A result other than NO is worth a yes only if
/// the key file's own check passed on the same bytes; unless the result is NO, `why` and `*place`
/// are `IF_TESTED_WHY`.
#[allow(clippy::too_many_arguments)]
pub fn check_entry_if_tested(
    c: &Configured,
    first: &UnprovedTable,
    file: &mut Reader<'_>,
    calls: &mut HashCalls,
    why: &mut Option<String>,
    notes: Option<&mut Notes>,
    place: Option<&mut Option<&'static str>>,
) -> IfTested {
    let mut place = place;
    let mut unused = TestedTable::default();
    let first_tested = first.as_if_tested();
    let verdict = check_entry(c, &first_tested, file, &mut unused, calls, why, notes, place.as_deref_mut());
    if verdict == ProofVerdict::No {
        return IfTested::No;
    }
    // Never null here, so that "no reason was given" cannot be taken for a yes.
    *why = Some(String::from(IF_TESTED_WHY));
    set_place(&mut place, Some(IF_TESTED_WHY));
    match verdict {
        ProofVerdict::Yes => IfTested::YesIfTheTableIsTested,
        ProofVerdict::YesWithWork => IfTested::YesWithWorkIfTheTableIsTested,
        ProofVerdict::No => unreachable!(),
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
    use crate::frame::heads::HEAD_TAG_KEY;
    use crate::frame::hiding_conditions::RangeCheck;
    use crate::frame::parameters::Parameters;
    use crate::iop::link::LINK_REFUSED_STEPS;
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

    fn record_bytes(fixed: &EntryFixed) -> usize {
        let shape = &fixed.link.table;
        (shape.rows() * shape.answers as u64) as usize * 24
    }

    /// A well-formed leaf file's table part: header, a zero root, zero answers.
    fn good_table(fixed: &EntryFixed) -> Vec<u8> {
        let mut v = header(HEAD_TAG_ENTRY, PROGRAM_VERSION_WORD);
        v.extend_from_slice(&[0u8; 32]);
        v.resize(v.len() + record_bytes(fixed), 0);
        v
    }

    #[test]
    fn entry_fault_reports_the_link_shape() {
        let c = configured();
        let mut under = entry_under(&c);
        assert_eq!(entry_fault(&under.plan, &under.fixed), None);
        under.fixed.link.columns_first = 0;
        assert_eq!(entry_fault(&under.plan, &under.fixed), Some("no column is drawn"));
    }

    #[test]
    fn a_short_header_refuses_the_entry() {
        let c = configured();
        let fixed = entry_fixed(&c);
        let mut key = IndexKey::default();
        let mut file = Reader::new(&[]);
        assert_eq!(
            read_entry_table_unproved(&fixed, &mut file, &mut key),
            Err("file-too-short")
        );
    }

    #[test]
    fn a_wrong_tag_refuses_the_entry() {
        let c = configured();
        let fixed = entry_fixed(&c);
        let mut key = IndexKey::default();
        let bytes = header(HEAD_TAG_KEY, PROGRAM_VERSION_WORD);
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_entry_table_unproved(&fixed, &mut file, &mut key),
            Err("file-of-another-kind")
        );
    }

    #[test]
    fn a_wrong_version_refuses_the_entry() {
        let c = configured();
        let fixed = entry_fixed(&c);
        let mut key = IndexKey::default();
        let bytes = header(HEAD_TAG_ENTRY, PROGRAM_VERSION_WORD ^ 1);
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_entry_table_unproved(&fixed, &mut file, &mut key),
            Err("version-unknown")
        );
    }

    #[test]
    fn a_missing_copy_root_refuses_the_entry() {
        let c = configured();
        let fixed = entry_fixed(&c);
        let mut key = IndexKey::default();
        let bytes = header(HEAD_TAG_ENTRY, PROGRAM_VERSION_WORD);
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_entry_table_unproved(&fixed, &mut file, &mut key),
            Err("the copy's root")
        );
    }

    #[test]
    fn a_short_record_refuses_the_entry() {
        let c = configured();
        let fixed = entry_fixed(&c);
        let mut key = IndexKey::default();
        let mut bytes = header(HEAD_TAG_ENTRY, PROGRAM_VERSION_WORD);
        bytes.extend_from_slice(&[0u8; 32]);
        bytes.extend_from_slice(&[0u8; 23]);
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_entry_table_unproved(&fixed, &mut file, &mut key),
            Err("the record's answers")
        );
    }

    #[test]
    fn an_entry_without_a_configuration_digest_is_refused() {
        let c = configured();
        let mut fixed = entry_fixed(&c);
        fixed.configuration = Digest::zero();
        let bytes = good_table(&fixed);
        let mut key = IndexKey::default();
        let mut file = Reader::new(&bytes);
        assert_eq!(
            read_entry_table_unproved(&fixed, &mut file, &mut key),
            Err("the key names no configuration")
        );
    }

    #[test]
    fn a_good_entry_table_is_read_and_the_file_stops_before_the_proof() {
        let c = configured();
        let fixed = entry_fixed(&c);
        let mut bytes = good_table(&fixed);
        bytes.push(0xcd);
        let mut key = IndexKey::default();
        let mut file = Reader::new(&bytes);
        assert_eq!(read_entry_table_unproved(&fixed, &mut file, &mut key), Ok(()));
        assert_eq!(key.made_under, *c.configuration());
        assert_eq!(key.root, Digest::zero());
        assert_eq!(key.table, fixed.link.table);
        assert!(!file.at_end());
        assert_eq!(file.take(1), Some(&[0xcd][..]));
        assert!(file.at_end());
    }

    #[test]
    fn the_configured_read_refuses_a_refused_configuration() {
        let c = configure(&[], &|_: &[&[u8]], _: &Parameters| Shapes::default());
        let mut table = UnprovedTable::default();
        let mut file = Reader::new(&[]);
        assert_eq!(
            read_entry_table_unproved_configured(&c, &mut file, &mut table),
            Err("the public files are not admitted")
        );
    }

    #[test]
    fn the_configured_read_fills_an_unproved_table() {
        let c = configured();
        let fixed = entry_fixed(&c);
        let bytes = good_table(&fixed);
        let mut table = UnprovedTable::default();
        let mut file = Reader::new(&bytes);
        assert_eq!(read_entry_table_unproved_configured(&c, &mut file, &mut table), Ok(()));
        assert_eq!(table.reader().made_under, *c.configuration());
        assert!(file.at_end());
    }

    #[test]
    fn a_leaf_file_without_its_link_proof_is_no_before_the_test() {
        // The table part is well formed, so LINK is built; its chain's salt is missing, so the
        // first folded-row message cannot be received.
        let c = configured();
        let fixed = entry_fixed(&c);
        let shape = fixed.link.table.clone();
        let first_key = IndexKey::new(
            shape.clone(),
            c.configuration(),
            &Digest::zero(),
            IndexRecord { y: vec![E::zero(); (shape.rows() * shape.answers as u64) as usize] },
        );
        let first = TestedTable::new_tested(
            first_key,
            &c.sized().d.set,
            key_public_bytes(&key_fixed(c.sized(), c.configuration())),
        );
        let mut entry = TestedTable::default();
        let bytes = good_table(&fixed);
        let mut file = Reader::new(&bytes);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let verdict = check_entry(
            &c,
            &first,
            &mut file,
            &mut entry,
            &mut calls,
            &mut why,
            None,
            Some(&mut place),
        );
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some(String::from("the chain's salt is missing")));
        assert_eq!(place, Some(LINK_REFUSED_STEPS));
        assert!(entry.tested_under().is_none());
    }

    #[test]
    fn check_entry_is_no_for_a_refused_configuration() {
        let c = configure(&[], &|_: &[&[u8]], _: &Parameters| Shapes::default());
        let first = TestedTable::default();
        let mut entry = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let verdict = check_entry(
            &c,
            &first,
            &mut file,
            &mut entry,
            &mut calls,
            &mut why,
            None,
            Some(&mut place),
        );
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(why, Some(String::from("the public files are not admitted")));
        assert_eq!(place, Some(ENTRY_PLACE_PARAMETERS));
    }

    #[test]
    fn an_untested_first_table_is_a_rejection_before_the_proof() {
        let c = configured();
        let first = TestedTable::default();
        let mut entry = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let verdict = check_entry(
            &c,
            &first,
            &mut file,
            &mut entry,
            &mut calls,
            &mut why,
            None,
            Some(&mut place),
        );
        assert_eq!(verdict, ProofVerdict::No);
        assert_eq!(
            why,
            Some(String::from(
                "the first table has passed no check: its key was refused, or was never checked"
            ))
        );
        assert_eq!(place, Some(ENTRY_PLACE_PARAMETERS));
    }

    #[test]
    fn an_entry_fault_is_the_reason_in_the_parameters() {
        let c = configured();
        let mut under = entry_under(&c);
        under.fixed.link.columns_first = 0;
        let first = TestedTable::default();
        let mut entry = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let good = check_entry_under(
            &under,
            &first,
            &mut file,
            &mut entry,
            &mut calls,
            &mut why,
            None,
            Some(&mut place),
        );
        assert!(!good);
        assert_eq!(why, Some(String::from("no column is drawn")));
        assert_eq!(place, Some(ENTRY_PLACE_PARAMETERS));
    }

    #[test]
    fn a_plan_that_does_not_hold_is_the_reason_in_the_parameters() {
        let c = configured();
        let mut f = FilePlan::default();
        let z = Sized { refused: String::from("made up"), ..Sized::default() };
        assert!(refused_file(&mut f, &z, &["link's chain"]));
        let under = EntryUnder {
            plan: f.chains[0].plan.clone(),
            fixed: entry_fixed(&c),
            key_public: Vec::new(),
        };
        assert_eq!(under.plan.why_not(), "made up");
        let first = TestedTable::default();
        let mut entry = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let good = check_entry_under(
            &under,
            &first,
            &mut file,
            &mut entry,
            &mut calls,
            &mut why,
            None,
            Some(&mut place),
        );
        assert!(!good);
        assert_eq!(why, Some(String::from(DOES_NOT_HOLD_WHY)));
        assert_eq!(place, Some(ENTRY_PLACE_PARAMETERS));
    }

    #[test]
    fn if_tested_is_no_for_an_unread_table() {
        let c = configured();
        let first = UnprovedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut place = None;
        let mut calls = HashCalls::default();
        let verdict = check_entry_if_tested(
            &c,
            &first,
            &mut file,
            &mut calls,
            &mut why,
            None,
            Some(&mut place),
        );
        assert_eq!(verdict, IfTested::No);
        assert_eq!(
            why,
            Some(String::from(
                "the first table has passed no check: its key was refused, or was never checked"
            ))
        );
    }

    #[test]
    #[should_panic(
        expected = "check_entry: the first table's key was checked under other public values"
    )]
    fn a_first_table_checked_under_other_public_values_ends_the_process() {
        let c = configured();
        let first =
            TestedTable::new_tested(IndexKey::default(), &c.sized().d.set, alloc::vec![1u8, 2, 3]);
        let mut entry = TestedTable::default();
        let mut file = Reader::new(&[]);
        let mut why = None;
        let mut calls = HashCalls::default();
        check_entry(
            &c,
            &first,
            &mut file,
            &mut entry,
            &mut calls,
            &mut why,
            None,
            None,
        );
    }
}
