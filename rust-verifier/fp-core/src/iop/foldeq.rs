//! FOLDEQ, ported from the verifier's side of `blocks/iop/foldeq.h`.
//!
//! A committed table is 2^v rows over F under one code, with a Merkle tree over its columns and a
//! record of out-of-domain answers. For a fold point gamma, FOLDEQ folds the rows into one oracle
//! message G_u, turns the row claims into claims on G_u's columns, checks the opened columns
//! against the table's root, and adds the record's claims. This port keeps the verifier-reachable
//! public data and checks: `tensor_below`, `VectorLay`, `IndexShape` with its fault and priced
//! table, `IndexRecord` with its seeds and bytes, the `PublicBytes` impls, `IndexReader` with
//! `IndexKey`, `index_name`, `index_tree`, `TableRead`, `record_value`, `block_sums`,
//! `FoldedWant`, `FoldeqShape`, the folded row and its record/column claims, and
//! `foldeq_columns_verify`, `foldeq_require` and `foldeq_verify`.
//!
//! Not ported, because only the prover's engine, coins and drafts use them: `IndexHolder`,
//! `foldeq_draft`, `foldeq_table` (an engine `Table`), `foldeq_columns_prove` and `foldeq_prove`.
//! The frame types `TestedTable`, `UnprovedTable`, `IfTested` and their pass-keys
//! (`blocks/frame/`) are not ported either; `TableRead` carries the optional `Setting` that a
//! tested table would hand in, and the caller supplies it through `TableRead::tested`.
//!
//! Deviations at the verifier's boundary: `IndexReader::read` takes the whole `VerifierRounds`
//! instead of a `Reader` and a `VerifierSession`, because the port's channel owns both borrows and
//! cannot lend them separately (the same adaptation as `receive_opening`); and the C++
//! `Plan::same_setting`, which has no port in `numbers/plan.rs`, is compared here field by field.
//! Hash calls are explicit, as everywhere else in the port.

use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;

use super::context::{OracleNotice, VerifierContext};
use super::message::Writer;
use super::relation::{
    Codes, GroupId, OracleId, OracleShape, Part, Row, RowKind, Statement, NONE_ID,
};
use super::send::{send_verify, AnswersRound};
use super::send_pad::send_pad;
use super::tensor::Tensor;
use crate::chain::public::PublicBytes;
use crate::chain::rounds::{record_seeds as record_seeds_chain, SampleSeed, VerifierRounds};
use crate::code::code::{code_ok, generator_at, Code};
use crate::field::ext::{F, E};
use crate::field::mle::{eq_index, eq_table, mle_eval, MleScalar};
use crate::hash::calls::HashCalls;
use crate::hash::modes::{salt_length_fits, Digest};
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::{PricedCode, PricedTable, TableDistances, TableTest};
use crate::numbers::round_names::R_LOC;
use crate::numbers::setting::Setting;
use crate::tree::opening::{check_opening, read_opening, Opening, OracleTreeShape};
use crate::tree::positions::PositionList;

/// `E_DEGREE`: a row over E has three entries over F per symbol.
pub const E_DEGREE: usize = 3;

// ---------------------------------------------------------------------------------------------------------------------
// Structured vectors: a cut, and how a vector is placed in a table
// ---------------------------------------------------------------------------------------------------------------------

/// Appends tensors whose sum is `v` with zero entries where the cut's index is at least `len`
/// (`tensor_below`, foldeq.h:71-114).
pub fn tensor_below(v: &Tensor, from: u32, count: u32, len: u64, out: &mut Vec<Tensor>) {
    assert!(
        from + count <= v.vars() && count < 64 && len <= (1u64 << count),
        "tensor_below: the cut does not fit the vector"
    );
    if len == (1u64 << count) {
        out.push(v.clone());
        return;
    }
    {
        let mut least = 0u64;
        let mut most = 0u64;
        for t in 0..count {
            let written = v.dense_vars.contains(&(from + t));
            if !written && v.lo(from + t).is_zero() {
                least |= 1u64 << t;
            }
            if written || !v.hi(from + t).is_zero() {
                most |= 1u64 << t;
            }
        }
        if most < len {
            out.push(v.clone());
            return;
        }
        if least >= len {
            return;
        }
    }
    let mut dense = 0u32;
    for &d in &v.dense_vars {
        if d >= from && d < from + count {
            dense += 1;
        }
    }
    if dense > 0 {
        assert!(
            dense == count,
            "tensor_below: the cut runs over written-out and product variables at once"
        );
        assert!(
            !v.is_held(),
            "tensor_below: a factor that only the engine holds is to be cut"
        );
        let full = 1u64 << v.dense_vars.len();
        let source = v.values.as_ref().expect("tensor_below: dense variables without a vector");
        let mut values: Vec<E> =
            source[v.first as usize..(v.first + full) as usize].to_vec();
        for (d, value) in values.iter_mut().enumerate() {
            let mut number = 0u64;
            for (i, &dv) in v.dense_vars.iter().enumerate() {
                if dv >= from && dv < from + count {
                    number |= (((d as u64) >> i) & 1) << (dv - from);
                }
            }
            if number >= len {
                *value = E::zero();
            }
        }
        let mut w = v.clone();
        w.set_values(Rc::new(values), 0);
        out.push(w);
        return;
    }
    let mut q = count;
    while q > 0 {
        q -= 1;
        if (len >> q) & 1 == 0 {
            continue;
        }
        let mut w = v.clone();
        for t in q + 1..count {
            if (len >> t) & 1 != 0 {
                let hi = w.hi(from + t);
                w.set_pair(from + t, E::zero(), hi);
            } else {
                let lo = w.lo(from + t);
                w.set_pair(from + t, lo, E::zero());
            }
        }
        let lo = w.lo(from + q);
        w.set_pair(from + q, lo, E::zero());
        out.push(w);
    }
}

/// How a vector is placed in an oracle message's main table (`VectorLay`, foldeq.h:126-149).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct VectorLay {
    pub row_bits: u32,
    pub place_bits: u32,
    pub rows_high: bool,
}

impl VectorLay {
    pub fn bits(&self) -> u32 {
        self.row_bits + self.place_bits
    }

    /// The table's index of entry `j` (`index`).
    pub fn index(&self, j: u64) -> u64 {
        assert!((j >> self.bits()) == 0, "lay: no such entry");
        if self.rows_high {
            (j >> self.place_bits) | ((j & ((1u64 << self.place_bits) - 1)) << self.row_bits)
        } else {
            j
        }
    }

    /// The inverse of `index` (`entry_at`).
    pub fn entry_at(&self, index: u64) -> u64 {
        if self.rows_high {
            (index >> self.row_bits) | ((index & ((1u64 << self.row_bits) - 1)) << self.place_bits)
        } else {
            index
        }
    }

    /// `v` as a structured vector on the table (`on_table`).
    pub fn on_table(&self, mut v: Tensor) -> Tensor {
        assert!(v.vars() <= self.bits(), "lay: the vector is longer than the table");
        v.insert_choice(v.vars(), self.bits() - v.vars(), 0);
        if self.rows_high {
            v.rotate(self.place_bits);
            for d in &mut v.dense_vars {
                *d = if *d >= self.place_bits {
                    *d - self.place_bits
                } else {
                    *d + self.row_bits
                };
            }
        }
        v
    }
}

/// `vector_lay` (foldeq.h:151-153). `s` must name a base code.
pub fn vector_lay(codes: &Codes, s: &OracleShape, rows_high: bool) -> VectorLay {
    VectorLay {
        row_bits: ceil_log2(s.main_rows as u64),
        place_bits: codes.base[s.code as usize].log_ell(),
        rows_high,
    }
}

/// How many leading entries of a vector lie in real rows and before every main-table place of the
/// oracle message's sample pad (`vector_room`, foldeq.h:157-166). Zero if the placement does not
/// fit the shape or the table's index has more than 60 bits.
pub fn vector_room(codes: &Codes, s: &OracleShape, rows_high: bool) -> u64 {
    let lay = vector_lay(codes, s, rows_high);
    if !rows_high && s.main_rows != (1usize << lay.row_bits) {
        return 0;
    }
    if lay.bits() > 60 {
        return 0;
    }
    let mut room = (s.main_rows as u64) << lay.place_bits;
    if s.answers > 0 {
        for p in send_pad(codes, s) {
            if p.part == Part::Main {
                room = core::cmp::min(room, lay.entry_at(p.index));
            }
        }
    }
    room
}

// ---------------------------------------------------------------------------------------------------------------------
// The committed table: what is public
// ---------------------------------------------------------------------------------------------------------------------

/// The shape of a committed table (`IndexShape`, foldeq.h:172-196).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexShape {
    pub code: Code,
    pub v: u32,
    pub answers: u32,
    pub salt_bytes: usize,
    pub distances: TableDistances,
}

impl Default for IndexShape {
    fn default() -> Self {
        IndexShape {
            code: Code { log_n: 0, ell: 0, r: 0 },
            v: 0,
            answers: 0,
            salt_bytes: crate::hash::modes::SALT_FLOOR_BYTES as usize,
            distances: TableDistances::default(),
        }
    }
}

impl IndexShape {
    pub fn rows(&self) -> u64 {
        1u64 << self.v
    }
    /// Entries at the end of a row's message, three for each answer.
    pub fn pads(&self) -> usize {
        E_DEGREE * self.answers as usize
    }
    /// Entries before the pads.
    pub fn plain(&self) -> usize {
        self.code.ell - self.pads()
    }
    pub fn pad_place(&self, answer: u32, t: u32) -> u64 {
        self.plain() as u64 + (E_DEGREE as u64) * answer as u64 + t as u64
    }
    pub fn cube_bits(&self) -> u32 {
        self.code.log_ell()
    }
}

/// What a plan's error bounds use of a table, as this run has it (`priced_table`,
/// foldeq.h:204-208).
pub fn priced_table(s: &IndexShape, test: TableTest) -> PricedTable {
    PricedTable {
        code: PricedCode {
            log_n: s.code.log_n,
            ell: s.code.ell as u64,
            r: s.code.r as u64,
        },
        v: s.v,
        answers: s.answers,
        distances: s.distances,
        test,
        said: true,
    }
}

/// Null, or what is wrong (`index_fault`, foldeq.h:210-217).
pub fn index_fault(s: &IndexShape) -> Option<&'static str> {
    if !code_ok(&s.code) {
        return Some("the table's numbers are not a code");
    }
    if s.v > 40 {
        return Some("the table has too many rows");
    }
    if s.pads() >= s.code.ell {
        return Some("a row has no room beside its pads");
    }
    if !salt_length_fits(s.salt_bytes as u64) {
        return Some("the leaves of the table's tree have no admitted salt");
    }
    if s.answers < 1 {
        return Some("the table's number of answers is below 1");
    }
    None
}

/// A table's record: one answer for each row and seed, by row and then by answer (`IndexRecord`,
/// foldeq.h:231-233).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct IndexRecord {
    pub y: Vec<E>,
}

/// The record's canonical bytes, with no length (`record_bytes`, foldeq.h:234-238).
pub fn record_bytes(rec: &IndexRecord) -> Vec<u8> {
    let mut w = Writer::default();
    for y in &rec.y {
        w.put_e(*y);
    }
    w.bytes().to_vec()
}

/// The seeds of the record of the table with this name (`record_seeds`, foldeq.h:241-243). The
/// chain itself is `chain::rounds::record_seeds` under `LABEL_RECORD`; this wrapper supplies the
/// table's cube and answer count.
pub fn record_seeds(s: &IndexShape, name: &[u8], calls: &mut HashCalls) -> Vec<SampleSeed> {
    record_seeds_chain(name, s.cube_bits(), s.answers, calls)
}

/// Null, or what is wrong with a record from a file (`record_fault`, foldeq.h:245-247).
pub fn record_fault(s: &IndexShape, rec: &IndexRecord) -> Option<&'static str> {
    if rec.y.len() as u128 != s.rows() as u128 * s.answers as u128 {
        Some("the record has not one answer for each row and seed")
    } else {
        None
    }
}

impl PublicBytes for SampleSeed {
    /// `public_bytes(Writer&, const SampleSeed&)` (foldeq.h:249).
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.z.len() as u64);
        for x in &self.z {
            w.put_e(*x);
        }
        w.put_e(self.beta);
    }
    /// `public_fault(const SampleSeed&)` (foldeq.h:256).
    fn public_fault(&self) -> Option<&'static str> {
        if self.beta == E::zero() {
            Some("a sample's seed has the factor 0 on its pad")
        } else {
            None
        }
    }
}

impl PublicBytes for IndexShape {
    /// `public_bytes(Writer&, const IndexShape&)` (foldeq.h:250-252).
    fn public_bytes(&self, w: &mut Writer) {
        self.code.public_bytes(w);
        w.put_u64(self.v as u64);
        w.put_u64(self.answers as u64);
        w.put_u64(self.salt_bytes as u64);
    }
    /// `public_fault(const IndexShape&)` (foldeq.h:257).
    fn public_fault(&self) -> Option<&'static str> {
        index_fault(self)
    }
}

impl PublicBytes for IndexRecord {
    /// `public_bytes(Writer&, const IndexRecord&)` (foldeq.h:253): a list of elements, with its
    /// length.
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.y.len() as u64);
        for y in &self.y {
            w.put_e(*y);
        }
    }
}

/// A table's item in a chain's first query: its commitment and its record (`IndexName`,
/// foldeq.h:262-267).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct IndexName {
    pub commitment: Vec<u8>,
    pub record: IndexRecord,
}

impl PublicBytes for IndexName {
    fn public_bytes(&self, w: &mut Writer) {
        self.commitment.public_bytes(w);
        self.record.public_bytes(w);
    }
    fn public_fault(&self) -> Option<&'static str> {
        if self.commitment.is_empty() {
            Some("a table without a commitment")
        } else {
            self.record.public_fault()
        }
    }
}

/// What a verifier has of a committed table (`IndexReader`, foldeq.h:271-297).
///
/// The C++ `read` takes a file reader and a session; this port takes the channel, whose two parts
/// cannot be borrowed separately. An implementation reads with `ch.file_only()` or checks a root
/// with `ch.session().record(..)`.
pub trait IndexReader {
    fn shape(&self) -> &IndexShape;
    fn record(&self) -> &IndexRecord;
    /// The bytes that commit to the table, for the first query of every chain on it.
    fn commitment(&self) -> Vec<u8>;
    /// The table's name; the commitment unless a reader says otherwise.
    fn name(&self) -> Vec<u8> {
        self.commitment()
    }
    /// Null, or how the reader contradicts itself.
    fn fault(&self) -> Option<&'static str> {
        None
    }
    /// The configuration digest from which the table's tree hashes start.
    fn configuration(&self) -> Digest {
        Digest::zero()
    }
    /// Reads the opening at `at` from the proof and checks it, leaving the columns in `columns`.
    fn read(
        &self,
        ch: &mut VerifierRounds<'_, '_, '_>,
        at: &PositionList,
        columns: &mut Vec<F>,
        calls: &mut HashCalls,
    ) -> bool;
}

/// The name of a table hashed as `index_tree` says (`index_name`, foldeq.h:303-309).
pub fn index_name(root: &Digest, s: &IndexShape, configuration: &Digest) -> Vec<u8> {
    let mut w = Writer::default();
    w.put_digest(root);
    w.put_digest(configuration);
    for x in [
        s.code.log_n as u64,
        s.code.ell as u64,
        s.code.r as u64,
        s.v as u64,
        s.answers as u64,
        s.salt_bytes as u64,
    ] {
        w.put_u64(x);
    }
    w.bytes().to_vec()
}

/// The tree over the columns: one part, 2^v symbols of F in a leaf (`index_tree`,
/// foldeq.h:312-319). It outlives every run, so its leaves start from the configuration digest.
pub fn index_tree(s: &IndexShape, configuration: &Digest) -> OracleTreeShape {
    let mut t = OracleTreeShape::default();
    t.log_n = s.code.log_n;
    t.main_symbols.push(s.rows() as usize);
    t.mask_symbols.push(0);
    t.tree_number = 0;
    t.salt_bytes = s.salt_bytes;
    t.stored = true;
    t.parameters = *configuration;
    t
}

/// `digest_bytes` (foldeq.h:321-325).
pub fn digest_bytes(d: &Digest) -> Vec<u8> {
    let mut w = Writer::default();
    w.put_digest(d);
    w.bytes().to_vec()
}

/// A table's key: the `IndexReader` of a table whose tree has the shape `index_tree` gives
/// (`IndexKey`, foldeq.h:328-349).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct IndexKey {
    pub table: IndexShape,
    pub made_under: Digest,
    pub root: Digest,
    pub rec: IndexRecord,
}

impl IndexKey {
    pub fn new(table: IndexShape, configuration: &Digest, root: &Digest, rec: IndexRecord) -> Self {
        IndexKey { table, made_under: *configuration, root: *root, rec }
    }
}

impl IndexReader for IndexKey {
    fn shape(&self) -> &IndexShape {
        &self.table
    }
    fn record(&self) -> &IndexRecord {
        &self.rec
    }
    fn commitment(&self) -> Vec<u8> {
        digest_bytes(&self.root)
    }
    fn name(&self) -> Vec<u8> {
        index_name(&self.root, &self.table, &self.made_under)
    }
    fn configuration(&self) -> Digest {
        self.made_under
    }
    fn fault(&self) -> Option<&'static str> {
        index_key_fault(self)
    }
    fn read(
        &self,
        ch: &mut VerifierRounds<'_, '_, '_>,
        at: &PositionList,
        columns: &mut Vec<F>,
        calls: &mut HashCalls,
    ) -> bool {
        let mut o = Opening::default();
        let tree = index_tree(&self.table, &self.made_under);
        if !read_opening(ch.file_only(), &tree, at, &mut o) {
            return false;
        }
        let root = self.root;
        if !check_opening(
            &root,
            &tree,
            at,
            &o,
            Some(ch.session().record(&root)),
            None,
            calls,
        ) {
            return false;
        }
        // The table has no mask rows: a column is its main symbols.
        *columns = o.columns;
        true
    }
}

/// Null, or what is wrong with a key from a file (`index_key_fault`, foldeq.h:351-356).
pub fn index_key_fault(key: &IndexKey) -> Option<&'static str> {
    if let Some(f) = index_fault(&key.table) {
        return Some(f);
    }
    if key.made_under == Digest::zero() {
        return Some("the key names no configuration");
    }
    record_fault(&key.table, &key.rec)
}

// ---------------------------------------------------------------------------------------------------------------------
// A table that has passed its test
// ---------------------------------------------------------------------------------------------------------------------

/// The argument type of the functions that read a table's columns (`TableRead`, foldeq.h:466-484).
/// It borrows the reader and, when a test has passed, the setting under which it passed.
#[derive(Clone, Copy)]
pub struct TableRead<'a> {
    reader_: &'a dyn IndexReader,
    under_: Option<&'a Setting>,
}

impl<'a> TableRead<'a> {
    /// A reader that counts as untested (`TableRead(const IndexReader&)`).
    pub fn untested(reader: &'a dyn IndexReader) -> Self {
        TableRead { reader_: reader, under_: None }
    }
    /// A reader with the setting under which its test passed (`TableRead(const TestedTable&)`).
    pub fn tested(reader: &'a dyn IndexReader, under: &'a Setting) -> Self {
        TableRead { reader_: reader, under_: Some(under) }
    }
    pub fn reader(&self) -> &'a dyn IndexReader {
        self.reader_
    }
    /// Null: no test has passed.
    pub fn tested_under(&self) -> Option<&'a Setting> {
        self.under_
    }
}

/// A table that has passed its test (`TestedTable`, foldeq.h:412-437). Apart from the crate's own
/// checkers, only `UnprovedTable::as_if_tested()` makes one that counts as tested; a default table
/// is untested.
#[derive(Clone, Debug, Default)]
pub struct TestedTable {
    key: IndexKey,
    under: Setting,
    key_public: Vec<u8>,
    tested: bool,
}

impl TestedTable {
    /// The crate's checkers make one after every chain of the file has been accepted.
    #[allow(dead_code)]
    pub(crate) fn new_tested(key: IndexKey, under: &Setting, key_public: Vec<u8>) -> Self {
        TestedTable { key, under: under.clone(), key_public, tested: true }
    }
    pub fn reader(&self) -> &IndexKey {
        &self.key
    }
    /// Null: no test has passed.
    pub fn tested_under(&self) -> Option<&Setting> {
        if self.tested { Some(&self.under) } else { None }
    }
    /// What `key_public_bytes()` gave at the key's check; a leaf table has the bytes of the key to
    /// which it is linked.
    pub fn key_public(&self) -> &[u8] {
        &self.key_public
    }
}

impl IndexReader for TestedTable {
    fn shape(&self) -> &IndexShape {
        self.key.shape()
    }
    fn record(&self) -> &IndexRecord {
        self.key.record()
    }
    fn commitment(&self) -> Vec<u8> {
        self.key.commitment()
    }
    fn name(&self) -> Vec<u8> {
        self.key.name()
    }
    fn configuration(&self) -> Digest {
        self.key.configuration()
    }
    fn fault(&self) -> Option<&'static str> {
        self.key.fault()
    }
    fn read(
        &self,
        ch: &mut VerifierRounds<'_, '_, '_>,
        at: &PositionList,
        columns: &mut Vec<F>,
        calls: &mut HashCalls,
    ) -> bool {
        self.key.read(ch, at, columns, calls)
    }
}

/// A table's reader taken from the first bytes of a key file or leaf file, without the proofs that
/// follow them (`UnprovedTable`, foldeq.h:444-464).
#[derive(Clone, Debug, Default)]
pub struct UnprovedTable {
    key: IndexKey,
    under: Setting,
    key_public: Vec<u8>,
    read_: bool,
}

impl UnprovedTable {
    #[allow(dead_code)]
    pub(crate) fn new_read(key: IndexKey, under: &Setting, key_public: Vec<u8>) -> Self {
        UnprovedTable { key, under: under.clone(), key_public, read_: true }
    }
    pub fn reader(&self) -> &IndexKey {
        &self.key
    }
    /// An unfilled table, as after a failed read that the caller ignored, gives an untested table.
    #[allow(dead_code)]
    pub(crate) fn as_if_tested(&self) -> TestedTable {
        if self.read_ {
            TestedTable::new_tested(self.key.clone(), &self.under, self.key_public.clone())
        } else {
            TestedTable::default()
        }
    }
}

/// `IfTested` (foldeq.h:400): a result other than NO is worth a yes only if the table's own files
/// pass; it converts to neither bool nor `ProofVerdict`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IfTested {
    No,
    YesIfTheTableIsTested,
    YesWithWorkIfTheTableIsTested,
}

/// What the two functions that return `IfTested` leave in `why` unless they reject
/// (`IF_TESTED_WHY`, foldeq.h:404-405).
pub const IF_TESTED_WHY: &str =
    "not refused; worth a yes only if the checks of the table's own files pass";

/// Whether a read's error bound needs a table that has passed an earlier test (`TableStanding`,
/// foldeq.h:486).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableStanding {
    UnderTest,
    AlreadyTested,
}

/// One answer of the record from one row's message (`record_value`, foldeq.h:492-497).
pub fn record_value<T: MleScalar>(
    s: &IndexShape,
    seed: &SampleSeed,
    answer: u32,
    message: &[T],
) -> E {
    let k = s.cube_bits() as usize;
    let mut sum = mle_eval(message, s.code.ell, &seed.z, k);
    for p in s.plain()..s.code.ell {
        sum -= eq_index(p as u64, &seed.z, k) * message[p].to_e();
    }
    for t in 0..E_DEGREE {
        sum += message[s.pad_place(answer, t as u32) as usize]
            .from_e_mul(seed.beta * E::theta(t));
    }
    sum
}

/// Sums over blocks of consecutive entries of a folded message (`BlockSums`, foldeq.h:505-510).
#[derive(Clone, Debug, Default)]
pub struct BlockSums {
    /// `k_lo` coordinates of the low point.
    pub low: Vec<E>,
    pub k_lo: u32,
    pub count: u64,
    pub sums: Vec<E>,
}

/// `sums[y] = sum_j eq(j, low) message[j + 2^k_lo y]` (`block_sums`, foldeq.h:511-518).
pub fn block_sums(message: &[E], b: &mut BlockSums) {
    assert!(
        (b.count << b.k_lo) <= message.len() as u64,
        "block sums: the blocks run beyond the message"
    );
    let mut weight = vec![E::zero(); 1usize << b.k_lo];
    eq_table(&b.low, b.k_lo as usize, &mut weight);
    b.sums = vec![E::zero(); b.count as usize];
    for y in 0..b.count {
        for (j, &w) in weight.iter().enumerate() {
            b.sums[y as usize] += w * message[j + ((y << b.k_lo) as usize)];
        }
    }
}

/// The form in which the prover's engine returns a folded row (`FoldedWant`, foldeq.h:525-528).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FoldedWant {
    pub rows: usize,
    pub len: usize,
    pub tail_first: u64,
}

// ---------------------------------------------------------------------------------------------------------------------
// The folded row inside G_u, and the claims on it
// ---------------------------------------------------------------------------------------------------------------------

/// FOLDEQ's public shape: `index` is the table's shape, `u` G_u's (`FoldeqShape`, foldeq.h:589-601).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldeqShape {
    pub index: IndexShape,
    pub u: OracleShape,
    pub rows_high: bool,
    pub leaf_class: u32,
    pub columns: u64,
}

impl Default for FoldeqShape {
    fn default() -> Self {
        FoldeqShape {
            index: IndexShape::default(),
            u: OracleShape::default(),
            rows_high: false,
            leaf_class: 0,
            columns: 0,
        }
    }
}

impl FoldeqShape {
    /// The next multiple of the least power of two that holds the tail (`tail_first`).
    pub fn tail_first(&self) -> u64 {
        let step = 1u64 << self.index.code.log_r();
        (self.index.code.ell as u64 + step - 1) / step * step
    }
    pub fn entries(&self) -> u64 {
        self.tail_first() + self.index.code.r as u64
    }
}

impl PublicBytes for FoldeqShape {
    /// `public_bytes(Writer&, const FoldeqShape&)` (foldeq.h:602-604).
    fn public_bytes(&self, w: &mut Writer) {
        self.index.public_bytes(w);
        self.u.public_bytes(w);
        w.put_u64(self.rows_high as u64);
        w.put_u64(self.leaf_class as u64);
        w.put_u64(self.columns);
    }
    /// `public_fault(const FoldeqShape&)` (foldeq.h:606-613).
    fn public_fault(&self) -> Option<&'static str> {
        if let Some(f) = index_fault(&self.index) {
            return Some(f);
        }
        if let Some(f) = self.u.public_fault() {
            return Some(f);
        }
        if self.u.main_rows == 0 || self.u.main_deg != E_DEGREE as u32 {
            return Some("the folded row's oracle message has no main rows over E");
        }
        if self.u.answers < 1 {
            return Some("the folded row's oracle message has no sample (answers = 0)");
        }
        if self.columns < 1 {
            return Some("no column is drawn");
        }
        None
    }
}

/// The same, and faults against the codes that the shape names (`foldeq_fault`, foldeq.h:615-620).
pub fn foldeq_fault(codes: &Codes, S: &FoldeqShape) -> Option<&'static str> {
    if let Some(f) = S.public_fault() {
        return Some(f);
    }
    if S.u.code as usize >= codes.base.len() {
        return Some("the folded row's oracle message names a code that is not there");
    }
    if S.entries() > vector_room(codes, &S.u, S.rows_high) {
        return Some("the folded row does not fit beside the pad of its oracle message");
    }
    None
}

/// G_u's number, and how a vector is placed in its main table (`FoldedRow`, foldeq.h:623-626).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FoldedRow {
    pub oracle: OracleId,
    pub lay: VectorLay,
}

impl Default for FoldedRow {
    fn default() -> Self {
        FoldedRow { oracle: NONE_ID, lay: VectorLay::default() }
    }
}

/// The value of the fold at a position, from the column there (`foldeq_symbol`, foldeq.h:629-633).
pub fn foldeq_symbol(eq_gamma: &[E], column: &[F]) -> E {
    let mut sum = E::zero();
    for r in 0..eq_gamma.len() {
        sum += eq_gamma[r] * column[r];
    }
    sum
}

/// Answer `i` of the record, folded into one claim on G_u (`foldeq_record_row`, foldeq.h:638-654).
pub fn foldeq_record_row(
    S: &FoldeqShape,
    seed: &SampleSeed,
    rec: &IndexRecord,
    i: u32,
    eq_gamma: &[E],
    at: &FoldedRow,
) -> Row {
    let s = &S.index;
    assert!(
        seed.z.len() == s.cube_bits() as usize
            && rec.y.len() as u128 == s.rows() as u128 * s.answers as u128,
        "record: not a record of this table"
    );
    let mut row = Row::plain("the record, folded");
    let under = Tensor::eq(&seed.z, s.cube_bits(), E::one());
    let mut cut = Vec::new();
    tensor_below(&under, 0, s.cube_bits(), s.code.ell as u64, &mut cut);
    for t in cut {
        row.add(at.oracle, Part::Main, at.lay.on_table(t));
    }
    for a in 0..s.answers {
        for t in 0..E_DEGREE as u32 {
            let p = s.pad_place(a, t);
            let coeff = if a == i {
                seed.beta * E::theta(t as usize)
            } else {
                E::zero()
            } - under.at(p);
            row.add_unit(at.oracle, Part::Main, at.lay.index(p), coeff);
        }
    }
    for r in 0..s.rows() {
        row.target += eq_gamma[r as usize] * rec.y[(r * s.answers as u64 + i as u64) as usize];
    }
    row
}

/// The claim on G_u that the folded codeword has the value `y` at the table's position `x`
/// (`foldeq_column_row`, foldeq.h:657-676).
pub fn foldeq_column_row(S: &FoldeqShape, x: u64, y: &E, at: &FoldedRow) -> Row {
    let c = &S.index.code;
    let g = generator_at(c, x);
    let mut row = Row::plain("a column of the table");
    row.kind = RowKind::Generator;
    let mut cut = Vec::new();
    tensor_below(
        &Tensor::product(&g.f, c.log_ell(), E::from_base(g.message_scale)),
        0,
        c.log_ell(),
        c.ell as u64,
        &mut cut,
    );
    for t in cut {
        row.add(at.oracle, Part::Main, at.lay.on_table(t));
    }
    if c.r > 0 {
        let mut tail = Vec::new();
        tensor_below(
            &Tensor::product(&g.f, c.log_r(), E::from_base(g.tail_scale)),
            0,
            c.log_r(),
            c.r as u64,
            &mut tail,
        );
        for mut t in tail {
            t.insert_choice(c.log_r(), at.lay.bits() - c.log_r(), S.tail_first() >> c.log_r());
            row.add(at.oracle, Part::Main, at.lay.on_table(t));
        }
    }
    row.target = *y;
    row
}

// ---------------------------------------------------------------------------------------------------------------------
// The block
// ---------------------------------------------------------------------------------------------------------------------

/// `eq_gamma[r] = eq(r, gamma)` (`foldeq_weights`, foldeq.h:697-701).
pub fn foldeq_weights(S: &FoldeqShape, gamma: &[E]) -> Vec<E> {
    let mut eq_gamma = vec![E::zero(); S.index.rows() as usize];
    eq_table(gamma, S.index.v as usize, &mut eq_gamma);
    eq_gamma
}

/// Both sides, once G_u is sent and sampled: G_u joins `g` with the record's claims
/// (`foldeq_joined`, foldeq.h:723-730). `calls` is the port's explicit hash counter; the C++
/// `record_seeds` draws without naming one.
#[allow(clippy::too_many_arguments)]
pub fn foldeq_joined(
    st: &mut Statement,
    S: &FoldeqShape,
    name: &[u8],
    rec: &IndexRecord,
    eq_gamma: &[E],
    oracle: OracleId,
    g: GroupId,
    calls: &mut HashCalls,
) -> FoldedRow {
    let at = FoldedRow { oracle, lay: vector_lay(st.codes(), &S.u, S.rows_high) };
    st.join(g, at.oracle, false);
    let seeds = record_seeds(&S.index, name, calls);
    for i in 0..S.index.answers {
        st.add_row(g, foldeq_record_row(S, &seeds[i as usize], rec, i, eq_gamma, &at));
    }
    at
}

/// Reads and checks the table's columns and adds one claim on G_u for each draw, repeats included
/// (`foldeq_columns_verify`, foldeq.h:744-787).
#[allow(clippy::too_many_arguments)]
pub fn foldeq_columns_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    table: &TableRead<'_>,
    test: TableTest,
    standing: TableStanding,
    S: &FoldeqShape,
    eq_gamma: &[E],
    list: &PositionList,
    at: &FoldedRow,
    g: GroupId,
    calls: &mut HashCalls,
) -> bool {
    let key = table.reader();
    // The plan's error bound for the round closed last must have been computed for this table and
    // the caller's `test`.
    V.ch.require_table(&priced_table(&S.index, test));
    assert!(
        test == TableTest::Link
            || (standing == TableStanding::AlreadyTested) == (test == TableTest::Later),
        "foldeq: the caller says that a one-time test reads a tested table, or a later test a table under test"
    );
    if standing == TableStanding::AlreadyTested {
        assert!(
            table.tested_under().is_some(),
            "foldeq: the error bound of this read needs a table that has passed its one-time test, and this reader has passed none: hand in what check_key or check_entry gave"
        );
        assert!(
            same_setting(table.tested_under().unwrap(), &V.ch.plan().set),
            "foldeq: the table was tested under another setting (target, work bits) than this run's: key, entry and proof must be checked under one Configured"
        );
    }
    // The reader's distances must be the run's. C++ also prints both values to stderr; a no_std
    // core has no stderr, so the panic message keeps the check's own text.
    assert!(
        key.shape().distances == S.index.distances,
        "foldeq: the table's reader names other distances than this run is sized at: key, entry and batch must come from one sized whole"
    );
    if !V.ch.ok() {
        return false;
    }
    assert!(
        list.draws().len() as u64 == S.columns && list.log_n() == S.index.code.log_n,
        "foldeq: the plan draws other columns than the shape says"
    );
    let rows = S.index.rows() as usize;
    let mut columns = Vec::new();
    if !key.read(&mut *V.ch, list, &mut columns, calls) || columns.len() != list.size() * rows {
        V.ch.refuse("the opened columns of the table do not lead to its root");
        return false;
    }
    for &x in list.draws() {
        let start = list.index_of(x) * rows;
        V.st.add_row(
            g,
            foldeq_column_row(S, x, &foldeq_symbol(eq_gamma, &columns[start..start + rows]), at),
        );
    }
    if V.notes.is_some() {
        // For comparing verifiers block by block; the notes change nothing.
        let first_x = list.draws()[0];
        let start = list.index_of(first_x) * rows;
        let first = foldeq_column_row(
            S,
            first_x,
            &foldeq_symbol(eq_gamma, &columns[start..start + rows]),
            at,
        );
        V.note("FOLDEQ: (Col_1)'s target", first.target);
        V.note(
            "FOLDEQ: (Col_1) on G_u<0>",
            first.coefficient(at.oracle, Part::Main, at.lay.index(0)),
        );
        if S.index.code.r != 0 {
            V.note(
                "FOLDEQ: (Col_1) on G_u<B>",
                first.coefficient(at.oracle, Part::Main, at.lay.index(S.tail_first())),
            );
        }
    }
    true
}

/// Verifier, before anything is read; shape and key are no parts of a proof, so a fault ends the
/// process (`foldeq_require`, foldeq.h:791-802).
pub fn foldeq_require(codes: &Codes, key: &dyn IndexReader, S: &FoldeqShape) {
    if let Some(f) = foldeq_fault(codes, S) {
        panic!("{}", f);
    }
    if let Some(f) = key.fault() {
        panic!("{}", f);
    }
    let fault = record_fault(&S.index, key.record());
    let shape = key.shape();
    // The reader's shape must equal the bound one in every bound member (all but `distances`).
    assert!(
        fault.is_none()
            && shape.code == S.index.code
            && shape.v == S.index.v
            && shape.answers == S.index.answers
            && shape.salt_bytes == S.index.salt_bytes,
        "{}",
        fault.unwrap_or("foldeq: another table's key")
    );
}

/// The verifier's side of FOLDEQ (`foldeq_verify`, foldeq.h:834-851). False rejects the proof;
/// true leaves the claims on G_u, now in `g`, to the proximity test.
#[allow(clippy::too_many_arguments)]
pub fn foldeq_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    table: &TableRead<'_>,
    S: &FoldeqShape,
    test: TableTest,
    gamma: &[E],
    g: GroupId,
    at: &mut FoldedRow,
    with: &[OracleNotice],
    with_ids: Option<&mut Vec<OracleId>>,
    calls: &mut HashCalls,
) -> bool {
    assert!(
        test != TableTest::Link,
        "foldeq: a link reads two tables: call link_verify() (iop/link.h)"
    );
    let key = table.reader();
    foldeq_require(V.st.codes(), key, S);
    let eq_gamma = foldeq_weights(S, gamma);
    let mut notices = Vec::with_capacity(1 + with.len());
    notices.push(OracleNotice { shape: S.u.clone(), leaf_class: S.leaf_class });
    notices.extend_from_slice(with);
    let (good, ids) = send_verify(V, &notices, AnswersRound::Own, calls);
    if !good {
        return false;
    }
    if let Some(out) = with_ids {
        out.clear();
        out.extend_from_slice(&ids[1..]);
    }
    let name = key.name();
    *at = foldeq_joined(&mut V.st, S, &name, key.record(), &eq_gamma, ids[0], g, calls);
    V.note("FOLDEQ: e_0", eq_gamma[0]);
    if V.notes.is_some() {
        let seeds = record_seeds(&S.index, &name, calls);
        V.note(
            "FOLDEQ: (Rec_0)'s target",
            foldeq_record_row(S, &seeds[0], key.record(), 0, &eq_gamma, at).target,
        );
    }
    let list = {
        let mut from = V.ch.close_positions(R_LOC, calls);
        // Must be the plan's table: see `priced_table`.
        from.require_table(&priced_table(&S.index, test));
        from.positions(S.index.code.log_n, calls)
    };
    foldeq_columns_verify(
        V,
        table,
        test,
        if test == TableTest::Later {
            TableStanding::AlreadyTested
        } else {
            TableStanding::UnderTest
        },
        S,
        &eq_gamma,
        &list,
        at,
        g,
        calls,
    )
}

/// `Plan::same_setting` (plan.h:497-507), which `numbers/plan.rs` does not port: every field of a
/// `Setting`, including the six by three work bits.
fn same_setting(a: &Setting, b: &Setting) -> bool {
    a.field_name == b.field_name
        && a.p == b.p
        && a.degree == b.degree
        && a.circle == b.circle
        && a.f_bytes == b.f_bytes
        && a.e_bytes == b.e_bytes
        && a.digest_bytes == b.digest_bytes
        && a.salt_bytes == b.salt_bytes
        && a.nonce_bytes == b.nonce_bytes
        && a.position_bytes == b.position_bytes
        && a.hash_block_bytes == b.hash_block_bytes
        && a.label_bytes == b.label_bytes
        && a.chain_extra_bytes == b.chain_extra_bytes
        && a.chain_free_words == b.chain_free_words
        && a.target == b.target
        && a.instances == b.instances
        && a.samples == b.samples
        && a.saved_coefficient == b.saved_coefficient
        && a.work == b.work
}
