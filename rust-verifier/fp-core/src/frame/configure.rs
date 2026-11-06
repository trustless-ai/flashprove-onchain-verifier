//! Turning a configuration's public files into what committer, prover and verifier run on, ported
//! from `blocks/frame/configure.h`.
//!
//! `configure` is the only function that makes a `Configured`. From the same bytes it computes the
//! configuration digest and reads the parameters, and it passes those bytes to the caller's
//! function (`ShapesOf`), which returns the shapes. Sizes and plans follow from the parameters and
//! the shapes. What is hashed and what is run are meant to have one source; they have it only if
//! that function keeps to the bytes, which nothing checks.
//!
//! Not ported: `on_a_tests_word` (a test-only helper under `BLK_TESTED_TABLE_FOR_A_TEST`).

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::frame::files::{
    file_entry, file_key, file_proof, merged, sized, FilePlan, Sized, Subproofs,
};
use crate::frame::heads::configuration_digest;
use crate::frame::heads::published_id as heads_published_id;
use crate::frame::hiding_conditions::{hiding_conditions_missed, RangeCheck, TableUse};
use crate::frame::key_fixed::{key_fault, key_fixed};
use crate::frame::parameters::{read_parameters, Parameters};
use crate::hash::calls::HashCalls;
use crate::hash::modes::Digest;
use crate::iop::foldeq::{record_seeds, IndexReader};
use crate::iop::lin::{LinBindingShape, LinShape};
use crate::iop::relation::Codes;
use crate::iop::req::ReqShape;
use crate::iop::req_rows::{req_layout_fault, ReqLayout};
use crate::numbers::accounting::account;
use crate::numbers::codes::ceil_log2;

/// The verdict of `check_proof`, `check_key` or `check_entry` on one file (`ProofVerdict`,
/// configure.h:38-50). `YES_WITH_WORK`: some round meets the target only because its proof of
/// work is counted; the party that relies on the file reads `bits_without` and decides whether so
/// many bits are enough.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ProofVerdict {
    #[default]
    No,
    Yes,
    YesWithWork,
}

/// What is fixed before a request is known (`RequestFixed`, configure.h:52-65). `lin`: the shape
/// of LIN, a batch's test on the committed table; `binding`: the shape of the Merkle tree over the
/// seals of a batch's first chains.
#[derive(Clone, Debug, Default)]
pub struct RequestFixed {
    pub configuration: Digest,
    pub codes: Codes,
    pub lin: LinShape,
    pub shape: ReqShape,
    pub layout: ReqLayout,
    /// One per segment (`link`): a sub-proof's part of the first chain.
    pub identifiers: Vec<u64>,
    /// Linear claims (`rows`) on the committed table left by segments.
    pub pending_rows: u64,
    pub binding: LinBindingShape,
}

/// What the caller's function reads from the public files (`Shapes`, configure.h:66-92).
#[derive(Default)]
pub struct Shapes {
    pub sub: Subproofs,
    pub layout: ReqLayout,
    pub identifiers: Vec<u64>,
    /// Of one request; they follow from the sub-proofs' shapes.
    pub range_checks: Vec<RangeCheck>,
    /// Not empty: why `configure` is to reject the files.
    pub refused: String,
}

/// The caller's function (`ShapesOf`, configure.h:92). It must depend on the public files only,
/// which nothing checks.
pub type ShapesOf<'a> = dyn Fn(&[&[u8]], &Parameters) -> Shapes + 'a;

/// A plain value: it keeps no function or pointer of the caller of `configure`, so it may be
/// copied and kept (`Configured`, configure.h:94-161). If `refused()` is not empty, which other
/// members are filled depends on where `configure` stopped.
#[derive(Clone, Debug, Default)]
pub struct Configured {
    refused_: String,
    sized_: Sized,
    proof_: FilePlan,
    key_: FilePlan,
    entry_: FilePlan,
    fixed_: RequestFixed,
    range_checks_: Vec<RangeCheck>,
    work_: [Work; 3],
}

/// Column counts of one committed table, the anchor or a leaf table (`TableColumns`,
/// configure.h:107-128).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TableColumns {
    pub bears: u64,
    pub one_time: u64,
    pub link_on_the_first: u64,
    pub link_on_the_further: u64,
    pub a_batch: u64,
    pub batches: u64,
}

/// For one file's chains (`Work`, configure.h:137-145). `needed`: some round meets the target only
/// with its proof of work. `bits_without`: -log2 of the largest round error with the work left
/// out; `bits`: that round's bits of proof of work.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Work {
    pub needed: bool,
    pub bits_without: f64,
    pub bits: u32,
}

impl Configured {
    /// Not empty: rejected; check first.
    pub fn refused(&self) -> &str {
        &self.refused_
    }
    pub fn parameters(&self) -> &Parameters {
        &self.sized_.par
    }
    pub fn sized(&self) -> &Sized {
        &self.sized_
    }
    /// `chains[i].plan`: the plan of chain i. Proof file and key file: three chains; leaf file:
    /// one.
    pub fn proof(&self) -> &FilePlan {
        &self.proof_
    }
    pub fn key(&self) -> &FilePlan {
        &self.key_
    }
    pub fn entry(&self) -> &FilePlan {
        &self.entry_
    }
    pub fn configuration(&self) -> &Digest {
        &self.fixed_.configuration
    }
    /// `bears`: how many columns of one table may be opened over its life. `one_time` to
    /// `a_batch`: the columns that one opening opens, counted when it is begun. `batches`: how many
    /// batches a leaf table allows after its own LINK proof.
    pub fn table_columns(&self) -> TableColumns {
        TableColumns {
            bears: crate::code::code::hiding_positions(&self.sized_.batch.s.fold.index.code),
            one_time: self.sized_.once.s.fold.columns,
            link_on_the_first: self.sized_.link.s.columns_first,
            link_on_the_further: self.sized_.link.s.columns_further,
            a_batch: self.sized_.batch.s.fold.columns,
            batches: self.sized_.batch.batches,
        }
    }
    pub fn fixed(&self) -> &RequestFixed {
        &self.fixed_
    }
    /// One request's approximate range checks, as `Shapes::range_checks` gave them, once
    /// `hiding_conditions_missed` has accepted them (empty if `configure` stopped earlier).
    pub fn range_checks(&self) -> &[RangeCheck] {
        &self.range_checks_
    }
    pub fn work_of_the_key(&self) -> &Work {
        &self.work_[1]
    }
    pub fn work_of_an_entry(&self) -> &Work {
        &self.work_[2]
    }
    /// The proof file's fields only, not the key file's or a leaf file's.
    pub fn needs_work(&self) -> bool {
        self.work_[0].needed
    }
    pub fn bits_without_work(&self) -> f64 {
        self.work_[0].bits_without
    }
    pub fn work(&self) -> u32 {
        self.work_[0].bits
    }
}

/// `configure` (configure.h:166-213). `files`: the public files' bytes, the parameter file first.
/// A rejection's reason, `refused()`, is a text for a log; every number in it follows from the
/// files if the caller's function keeps to them (not checked).
pub fn configure(files: &[&[u8]], shapes: &ShapesOf<'_>) -> Configured {
    let mut calls = HashCalls::default();
    configure_with_calls(files, shapes, &mut calls)
}

/// `configure` with the caller's hash-call counter, so that a run's `q_V` includes the
/// configuration digest and every hash that the file plans make.
pub fn configure_with_calls(
    files: &[&[u8]],
    shapes: &ShapesOf<'_>,
    calls: &mut HashCalls,
) -> Configured {
    let mut c = Configured::default();
    let mut par = Parameters::default();
    if files.is_empty() {
        c.refused_ = String::from("no parameter file");
        return c;
    }
    if let Err(why) = read_parameters(files[0], &mut par) {
        c.refused_ = why;
        return c;
    }
    let mut s = shapes(files, &par);
    if !s.refused.is_empty() {
        c.refused_ = s.refused;
        return c;
    }
    let sub = &s.sub; // its functions are called here and stored nowhere
    c.sized_ = sized(&par, sub);
    if !c.sized_.refused.is_empty() {
        c.refused_ = c.sized_.refused.clone();
        return c;
    }
    let mut last = 0u64;
    c.proof_ = file_proof(&c.sized_, sub, false, &mut last);
    c.key_ = file_key(&c.sized_, false, &mut last);
    c.entry_ = file_entry(&c.sized_, false, &mut last);
    let files_ = [&c.proof_, &c.key_, &c.entry_];
    for (file, f) in files_.iter().enumerate() {
        for chain in &f.chains {
            let where_ = format!("{}, {}", f.name, chain.name);
            if !chain.plan.holds() {
                // No file is worth anything under such parameters.
                c.refused_ = format!("{}: {}", where_, chain.plan.why_not());
                return c;
            }
            if !chain.plan.names_of_the_format() {
                c.refused_ = format!("{}: a round has a name that is none of the format's", where_);
                return c;
            }
        }
        let whole = merged(&c.sized_.d.set, core::slice::from_ref(*f));
        if whole.refused() {
            // A chain's errors were computed under a `Setting` other than the file's.
            c.refused_ = format!("{}: {}", f.name, whole.why_not());
            return c;
        }
        let a = account(&whole, -1);
        c.work_[file] = Work {
            needed: a.needs_work,
            bits_without: a.lists.bits,
            bits: a.lists.work,
        };
    }
    // Committer, prover and verifier alike reject files that miss a condition for hiding, before a
    // table is made. A verifier cannot see a missed condition in a proof; but here anyone who
    // relies on a key file learns that its committer's files are outside the conditions under
    // which hiding is argued. How often the one-time test and the LINK proofs were begun on a
    // table is not in the files (this call takes the default `TableUse`).
    {
        let missed = hiding_conditions_missed(&c.sized_, sub, &s.range_checks, &TableUse::default());
        if !missed.is_empty() {
            c.refused_ = format!("hiding: {}", missed);
            return c;
        }
        c.range_checks_ = s.range_checks;
    }
    c.fixed_.configuration = configuration_digest(files, calls);
    {
        let fixed = key_fixed(&c.sized_, &c.fixed_.configuration);
        if let Some(fault) = key_fault(&fixed) {
            // Rejected here, before a table is committed, with the reason from `key_fault`.
            c.refused_ = format!("key: {}", fault);
            return c;
        }
    }
    let fixed = &mut c.fixed_;
    fixed.codes = c.sized_.proof_codes.clone();
    fixed.lin = c.sized_.batch.s.clone();
    fixed.shape = c.sized_.request.clone();
    fixed.layout = core::mem::take(&mut s.layout);
    fixed.identifiers = core::mem::take(&mut s.identifiers);
    fixed.pending_rows = s.sub.pending_rows;
    fixed.binding.log_leaves = ceil_log2(par.slots);
    fixed.binding.salt_bytes = c.sized_.d.set.salt_bytes as usize;
    // Conditions on several of these values together.
    if fixed.identifiers.len() != fixed.shape.link.len() {
        c.refused_ = String::from("the links' identifiers are not one for each link");
        return c;
    }
    if fixed.shape.at_start.len() != 1 {
        c.refused_ = String::from(
            "a request's first message holds one message of masks for its rows on the table",
        );
        return c;
    }
    if fixed.pending_rows == 0 {
        c.refused_ = String::from("a request leaves no row on the table");
        return c;
    }
    for l in 0..fixed.shape.link.len() {
        let want = if l + 1 == fixed.shape.link.len() { 1 } else { 0 };
        if fixed.shape.link[l].plain != want {
            c.refused_ = String::from(
                "the reply is one plain scalar of the last link, and no other link has one",
            );
            return c;
        }
    }
    if let Some(fault) = req_layout_fault(&fixed.codes, &fixed.shape, &fixed.layout) {
        c.refused_ = String::from(fault);
        return c;
    }
    c
}

/// The commitment ID (`heads.h`) of the commitment whose anchor `first_table` reads (`published_id`,
/// configure.h:215-222). Not checked: that it is the anchor. The reader's configuration digest is
/// the caller's own, not a file's: a mismatch with `c`'s, a `fault()` or a rejected `c` is a bug,
/// and the process ends. `calls` receives the hash calls of the ID (C++ counts them in the stage).
pub fn published_id(
    c: &Configured,
    first_table: &dyn IndexReader,
    calls: &mut HashCalls,
) -> Digest {
    assert!(
        c.refused().is_empty(),
        "published_id: the public files are not admitted"
    );
    assert!(
        first_table.fault().is_none() && first_table.configuration() == *c.configuration(),
        "published_id: the table's reader was formed under other public files, or contradicts itself"
    );
    let name = first_table.name();
    let seeds = record_seeds(first_table.shape(), &name, calls);
    let answers = &first_table.record().y;
    heads_published_id(c.configuration(), &name, &seeds, answers, calls)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_empty_file_list_is_rejected() {
        let c = configure(&[], &|_: &[&[u8]], _: &Parameters| Shapes::default());
        assert_eq!(c.refused(), "no parameter file");
        assert!(c.range_checks().is_empty());
    }

    /// A parameter file that `read_parameters` accepts (the sample of `parameters.rs`).
    fn sample_parameters() -> Vec<u8> {
        let mut s = String::new();
        s.push_str("version H821\nsec 100\nreading 1\nrowcost 1\nslots 4\nanswers 1\nrecord 1\n");
        for k in ["field", "sample", "closeness", "positions", "smallness"] {
            s.push_str(&format!("work {} 0 0 0\n", k));
        }
        s.push_str("salt 48\nlisted 0\n");
        for name in [
            "link", "folded", "omega", "own", "once-folded", "once-omega", "once-own",
            "once-ranges",
        ] {
            s.push_str(&format!("group {} 1 8 4 7 3\n", name));
            s.push_str(&format!("stages {} 4 3 8 7 2 1 6 5 0 0 0 0\n", name));
        }
        s.push_str("ranges-part 6\ntable 12 16 100 8 0 16\n");
        s.into_bytes()
    }

    fn a_key_for(configuration: &Digest) -> crate::iop::foldeq::IndexKey {
        use crate::code::code::Code;
        use crate::field::ext::E;
        use crate::iop::foldeq::{IndexKey, IndexRecord, IndexShape};
        let shape = IndexShape {
            code: Code { log_n: 8, ell: 16, r: 4 },
            v: 4,
            answers: 1,
            salt_bytes: 40,
            ..IndexShape::default()
        };
        let rec = IndexRecord { y: alloc::vec![E::zero(); 16] };
        IndexKey::new(shape, configuration, &Digest { w: [9; 8] }, rec)
    }

    #[test]
    fn published_id_checks_the_reader_and_names_the_commitment() {
        let configuration = Digest { w: [7; 8] };
        let c = Configured {
            fixed_: RequestFixed { configuration, ..RequestFixed::default() },
            ..Configured::default()
        };
        let key = a_key_for(&configuration);
        let mut calls = HashCalls::default();
        let name = key.name();
        let seeds = record_seeds(key.shape(), &name, &mut calls);
        let want = heads_published_id(&configuration, &name, &seeds, &key.record().y, &mut calls);
        let mut calls = HashCalls::default();
        assert_eq!(published_id(&c, &key, &mut calls), want);
    }

    #[test]
    #[should_panic(expected = "published_id: the public files are not admitted")]
    fn published_id_refuses_a_rejected_configuration() {
        let c = Configured { refused_: String::from("no"), ..Configured::default() };
        published_id(&c, &a_key_for(&Digest { w: [7; 8] }), &mut HashCalls::default());
    }

    #[test]
    #[should_panic(
        expected = "published_id: the table's reader was formed under other public files, or contradicts itself"
    )]
    fn published_id_refuses_another_configurations_table() {
        let c = Configured {
            fixed_: RequestFixed { configuration: Digest { w: [7; 8] }, ..RequestFixed::default() },
            ..Configured::default()
        };
        published_id(&c, &a_key_for(&Digest { w: [8; 8] }), &mut HashCalls::default());
    }

    #[test]
    fn a_shapes_refusal_stops_before_sizing() {
        let p = sample_parameters();
        let c = configure(
            &[&p],
            &|_: &[&[u8]], _: &Parameters| Shapes {
                refused: String::from("no shapes today"),
                ..Shapes::default()
            },
        );
        assert_eq!(c.refused(), "no shapes today");
        assert!(c.sized().par.table_data == 0);
    }
}
