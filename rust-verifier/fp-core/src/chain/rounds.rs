//! The channel through which a verifier reads a proof, ported from the verifier side of
//! `blocks/chain/rounds.h`.
//!
//! `VerifierRounds` follows a plan: every `close_..()` names the next planned round and checks
//! the prover message's bytes, roots and answers, the number of elements drawn and the work bits.
//! A mistake of the calling program panics; whatever depends on a proof's bytes makes `ok()` false
//! and every later read and draw a fixed value. The handle types borrow the channel, which is the
//! port's form of C++'s rule that a handle dies at the next item, close or seal.
//!
//! The C++ channel can print diagnostics (stderr) before a guard ends the process; a `no_std` core
//! has no stderr, so the diagnostics are part of the panic message. The hash calls are explicit.

use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::Cell;

use super::chain::{first_query_run, Chain, ChainKind, FirstQuery, LABEL_RECORD};
use super::public::{Binder, ChainFate, Public, PublicMark, Sealed, SharedFate};
use super::session::VerifierSession;
use crate::field::ext::{F, E};
use crate::hash::calls::HashCalls;
use crate::hash::modes::{ChainPrefix, Digest};
use crate::iop::message::Reader;
use crate::numbers::plan::{Cursor, PlanRound, Planned, PricedGroup, PricedTable};
use crate::numbers::setting::RoundKind;
use crate::tree::positions::PositionList;

/// The seed of an out-of-domain sample (`SampleSeed`).
#[derive(Clone, Debug)]
pub struct SampleSeed {
    pub z: Vec<E>,
    pub beta: E,
}

impl Default for SampleSeed {
    fn default() -> Self {
        SampleSeed { z: Vec::new(), beta: E::one() }
    }
}

/// The seeds whose answers are a committed table's record (`record_seeds`).
pub fn record_seeds(
    commitment: &[u8],
    variables: u32,
    answers: u32,
    calls: &mut HashCalls,
) -> Vec<SampleSeed> {
    let q = FirstQuery {
        label: LABEL_RECORD,
        parameters: Digest::zero(),
        statement: commitment.to_vec(),
        record: Vec::new(),
        salted: false,
        salt_in_proof: true,
        salt: Digest::zero(),
    };
    let mut c = Chain::new(&q, calls);
    let mut m = c.message(calls);
    let p = Chain::prefix(&mut m, ChainKind::Seed, 0);
    c.step(&p, 0, 0, calls);
    let mut seeds = Vec::with_capacity(answers as usize);
    for _ in 0..answers {
        let mut s = SampleSeed::default();
        s.z.reserve(variables as usize);
        for _ in 0..variables {
            s.z.push(c.draw_e(calls));
        }
        s.beta = c.draw_e_nonzero(calls);
        seeds.push(s);
    }
    seeds
}

/// A root as the verifier received it (`SentRoot`).
#[derive(Clone, Debug, Default)]
pub struct SentRoot {
    digest: Digest,
    run: Digest,
    configuration: Digest,
    sender: Option<PublicMark>,
}

impl SentRoot {
    pub fn digest(&self) -> &Digest {
        &self.digest
    }
    pub fn run(&self) -> &Digest {
        &self.run
    }
    pub fn configuration(&self) -> &Digest {
        &self.configuration
    }
}

const ASKED_ROWS: u32 = 1;
const ASKED_FIRST_LIST: u32 = 2;
const ASKED_GROUP: u32 = 4;
const ASKED_TABLE: u32 = 8;
const ASKED_COMBINATIONS: u32 = 16;
const ASKED_SHARING: u32 = 32;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Item {
    Plain,
    Root,
    Answer,
    HidingSum,
}

trait Takeable: Default {
    fn take_from(r: &mut Reader<'_>) -> Option<Self>;
    fn append_to(&self, m: &mut Vec<u8>);
}

impl Takeable for F {
    fn take_from(r: &mut Reader<'_>) -> Option<Self> {
        r.get_f()
    }
    fn append_to(&self, m: &mut Vec<u8>) {
        m.extend_from_slice(&self.to_bytes());
    }
}
impl Takeable for E {
    fn take_from(r: &mut Reader<'_>) -> Option<Self> {
        r.get_e()
    }
    fn append_to(&self, m: &mut Vec<u8>) {
        m.extend_from_slice(&self.to_bytes());
    }
}
impl Takeable for Digest {
    fn take_from(r: &mut Reader<'_>) -> Option<Self> {
        r.get_digest()
    }
    fn append_to(&self, m: &mut Vec<u8>) {
        m.extend_from_slice(&self.to_bytes());
    }
}
impl Takeable for u64 {
    fn take_from(r: &mut Reader<'_>) -> Option<Self> {
        r.get_u64()
    }
    fn append_to(&self, m: &mut Vec<u8>) {
        m.extend_from_slice(&self.to_le_bytes());
    }
}

/// The verifier's side of a chain (`VerifierRounds`).
pub struct VerifierRounds<'a, 'd, 's> {
    plan: Rc<Planned>,
    cursor: Cursor,
    chain: Option<Chain>,
    message: Vec<u8>,
    roots: u32,
    answers: u32,
    owed: u32,
    outside: usize,
    last_was_hiding_sum: bool,
    marks: Vec<PublicMark>,
    fate: SharedFate,
    earlier_fates: Vec<SharedFate>,
    has_run: bool,
    run: Digest,
    configuration: Digest,
    sealed: bool,
    lent: bool,
    closes: u64,
    entry: Option<usize>,
    drawn_e: u64,
    drawn_nonzero: u64,
    drawn_trits: u64,
    positions_done: bool,
    asked: u32,
    r: &'a mut Reader<'d>,
    session: &'s mut VerifierSession,
    why: Option<&'static str>,
}

impl<'a, 'd, 's> VerifierRounds<'a, 'd, 's> {
    /// Reads the chain's salt from `proof`, unless the Binder sets or omits it (`VerifierRounds`).
    pub fn new(
        binder: &mut Binder,
        proof: &'a mut Reader<'d>,
        session: &'s mut VerifierSession,
        calls: &mut HashCalls,
    ) -> Self {
        let plan = binder.plan();
        assert!(
            plan.set.nonce_bytes >= 1
                && plan.set.nonce_bytes <= 8
                && plan.set.position_bytes == 0,
            "rounds: a nonce has 1 to 8 bytes, and a proof lists no position"
        );
        let cursor = Cursor::new(plan.clone());
        let q = binder.first_query(&Digest::zero(), calls);
        assert!(q.label >> 32 == 0, "rounds: a protocol's label is below 2^32");
        let mut why: Option<&'static str> = None;
        let mut q = q;
        if q.salted && q.salt_in_proof {
            match proof.get_digest() {
                Some(salt) => q.salt = salt,
                None => {
                    q.salt = Digest::zero();
                    why = Some("the chain's salt is missing");
                    proof.refuse();
                }
            }
        }
        let chain = Chain::new(&q, calls);
        let has_run = q.salted;
        let mut run = Digest::zero();
        if has_run {
            run = first_query_run(&q, calls);
            if run == Digest::zero() {
                if why.is_none() {
                    why = Some("a chain's run's value is the digest of zeros");
                }
                proof.refuse();
                run.w[0] = 1;
            }
        }
        let configuration = binder.configuration_digest();
        let mut marks = Vec::with_capacity(1 + binder.earlier.len());
        marks.push(binder.mark.clone());
        marks.extend(binder.earlier.iter().cloned());
        let earlier_fates = binder.earlier_fates.clone();
        for f in &earlier_fates {
            assert!(
                session.holds(f),
                "rounds: a chain follows a chain of another session"
            );
        }
        let fate: SharedFate = Rc::new(Cell::new(ChainFate::default()));
        session.enter(fate.clone());
        let mut this = VerifierRounds {
            plan,
            cursor,
            chain: Some(chain),
            message: Vec::new(),
            roots: 0,
            answers: 0,
            owed: 0,
            outside: 0,
            last_was_hiding_sum: false,
            marks,
            fate,
            earlier_fates,
            has_run,
            run,
            configuration,
            sealed: false,
            lent: false,
            closes: 0,
            entry: None,
            drawn_e: 0,
            drawn_nonzero: 0,
            drawn_trits: 0,
            positions_done: false,
            asked: 0,
            r: proof,
            session,
            why,
        };
        if this.follows_a_refusal() {
            this.fail("an earlier chain of this proof was refused");
        }
        this
    }

    pub fn session(&mut self) -> &mut VerifierSession {
        self.session
    }

    pub fn ok(&self) -> bool {
        self.why.is_none() && self.r.ok() && !self.follows_a_refusal()
    }

    /// The first reason for a rejection (`why`). Every text that a channel records is a static
    /// string, so callers may keep the reason after the channel is dropped.
    pub fn why(&self) -> Option<&'static str> {
        if let Some(w) = self.why {
            Some(w)
        } else if !self.r.ok() {
            Some("an opening, or another answer to the verifier's queries, is cut short or not in canonical form")
        } else if self.follows_a_refusal() {
            Some("an earlier chain of this proof was refused")
        } else {
            None
        }
    }

    /// Reports a failed check that the caller made itself (`refuse`).
    pub fn refuse(&mut self, why: &'static str) {
        let w = if self.r.ok() {
            why
        } else {
            "an opening, or another answer to the verifier's queries, is cut short or not in canonical form"
        };
        self.fail(w);
    }

    /// For a caller whose read through `file_only()` has just failed (`refuse_what_was_read`).
    pub fn refuse_what_was_read(&mut self, why: &'static str) {
        self.fail(why);
    }

    pub fn recv_f(&mut self, x: &mut F) -> bool {
        self.item(Item::Plain);
        self.take(x)
    }

    pub fn recv_e(&mut self, x: &mut E) -> bool {
        self.item(Item::Plain);
        self.take(x)
    }

    pub fn recv_u64(&mut self) -> Option<u64> {
        self.item(Item::Plain);
        let mut x = 0u64;
        if !self.ok() {
            return None;
        }
        if !self.take(&mut x) {
            return None;
        }
        Some(x)
    }

    /// After a rejection, or if the root is missing, `root` is the default `SentRoot`.
    pub fn recv_root(&mut self, root: &mut SentRoot) -> bool {
        self.item(Item::Root);
        let mut d = Digest::zero();
        *root = SentRoot::default();
        if !self.take(&mut d) {
            return false;
        }
        *root = SentRoot {
            digest: d,
            run: self.run,
            configuration: self.configuration,
            sender: Some(self.marks[0].clone()),
        };
        true
    }

    /// Whether this chain, or one that it follows, has received the root (`received`).
    pub fn received(&self, root: &SentRoot) -> bool {
        match &root.sender {
            Some(s) => self.marks.iter().any(|m| Rc::ptr_eq(m, s)),
            None => false,
        }
    }

    pub fn recv_answer(&mut self, y: &mut E) -> bool {
        self.item(Item::Answer);
        self.take(y)
    }

    pub fn recv_hiding_sum(&mut self, sum: &mut E) -> bool {
        self.item(Item::HidingSum);
        self.take(sum)
    }

    pub fn file_only(&mut self) -> &mut Reader<'d> {
        self.r
    }

    /// True if and only if nothing was rejected and every byte of the proof was read (`finish`).
    pub fn finish(&mut self) -> bool {
        if self.ok() {
            self.end();
            if !self.r.at_end() {
                self.fail("bytes are left over at the end of the proof");
            }
        }
        self.ended()
    }

    /// `finish()` for a chain after which the file continues with another chain's bytes.
    pub fn finish_inside_a_file(&mut self) -> bool {
        if self.ok() {
            self.end();
        }
        self.ended()
    }

    pub fn close_algebraic(&mut self, name: &str, calls: &mut HashCalls) -> AlgebraicDraw<'_, 'a, 'd, 's> {
        self.close(name, RoundKind::Algebraic, calls);
        AlgebraicDraw { r: self }
    }

    /// The one element of E that joins a hiding polynomial to a claim (`close_epsilon`).
    pub fn close_epsilon(&mut self, name: &str, calls: &mut HashCalls) -> E {
        assert!(
            !self.ok() || self.last_was_hiding_sum,
            "rounds: the hiding polynomial's sum must be the last thing sent before this element"
        );
        self.close(name, RoundKind::Epsilon, calls);
        if self.ok() {
            assert!(
                self.entry().draw_e == 1,
                "rounds: the round is not planned with this element alone"
            );
        }
        self.element(false, calls)
    }

    pub fn close_empty(&mut self, name: &str, calls: &mut HashCalls) {
        assert!(
            !self.ok() || self.roots == 0,
            "rounds: a root stands in the query of the next verifier's message that is not empty"
        );
        self.close(name, RoundKind::Empty, calls);
    }

    pub fn close_seed(&mut self, name: &str, calls: &mut HashCalls) -> SeedDraw<'_, 'a, 'd, 's> {
        self.close(name, RoundKind::Seed, calls);
        SeedDraw { r: self }
    }

    pub fn close_positions(&mut self, name: &str, calls: &mut HashCalls) -> PositionsDraw<'_, 'a, 'd, 's> {
        self.close(name, RoundKind::Positions, calls);
        PositionsDraw { r: self }
    }

    pub fn close_bits(&mut self, name: &str, calls: &mut HashCalls) -> BitsDraw<'_, 'a, 'd, 's> {
        self.close(name, RoundKind::Bits, calls);
        BitsDraw { r: self }
    }

    /// Ends the chain with a seal (`seal`).
    pub fn seal(&mut self, name: &str, calls: &mut HashCalls) -> (bool, Sealed) {
        assert!(
            !self.ok() || self.roots == 0,
            "rounds: a root stands in the query of a verifier's message that is drawn for the protocol, not of a seal"
        );
        self.close(name, RoundKind::Seal, calls);
        let mut digest = Digest::zero();
        for i in 0..4 {
            let w = self.word(calls);
            digest.w[2 * i] = w as u32;
            digest.w[2 * i + 1] = (w >> 32) as u32;
        }
        self.sealed = true;
        if !self.ok() {
            let mut f = self.fate.get();
            f.refused = true;
            self.fate.set(f);
        }
        let mut fates = Vec::with_capacity(1 + self.earlier_fates.len());
        fates.push(self.fate.clone());
        fates.extend(self.earlier_fates.iter().cloned());
        let out = Sealed::new(self.marks.clone(), digest, fates, self.configuration);
        (self.ok(), out)
    }

    /// Reads a public input (`get`).
    pub fn get<'x, T>(&self, x: &'x Public<T>) -> &'x T {
        let mine = match x.mark() {
            Some(m) => self.marks.iter().any(|k| Rc::ptr_eq(k, m)),
            None => false,
        };
        assert!(
            mine && x.is_bound(),
            "rounds: a public input that does not stand in this chain's first query"
        );
        x.value().unwrap()
    }

    /// The round closed last batches `rows` linear claims (`require_rows`).
    pub fn require_rows(&mut self, rows: u64) {
        if self.ok() {
            assert!(
                self.entry().rows == rows,
                "rounds: the round batches another number of rows than its planned error counts"
            );
        }
        self.asked |= ASKED_ROWS;
    }

    pub fn require_first_list(&mut self, draws: u64) {
        if self.ok() {
            let e = self.entry();
            assert!(
                e.first_list != 0 && e.first_list == draws,
                "rounds: the round's first list has another number of draws than its planned error counts"
            );
        }
        self.asked |= ASKED_FIRST_LIST;
    }

    pub fn require_group(&mut self, run: &PricedGroup) {
        if self.ok() {
            let e = self.entry();
            assert!(
                e.group.said && e.group.same_run(run),
                "rounds: the round begins a stage on another group than its planned errors are priced for, or the plan names none"
            );
        }
        self.asked |= ASKED_GROUP;
    }

    pub fn require_codes(&mut self, run: &PricedGroup) {
        if self.ok() {
            let e = self.entry();
            assert!(
                e.group.said && e.group.same_run(run),
                "rounds: the round draws positions on rows of other codes than its planned error is priced for, or the plan names none"
            );
        }
        self.asked |= ASKED_GROUP;
    }

    pub fn require_table(&mut self, run: &PricedTable) {
        if self.ok() {
            let e = self.entry();
            assert!(
                e.table.said && e.table.same_run(run),
                "rounds: the round draws columns of another table than its planned error is priced for, or the plan names none"
            );
        }
        self.asked |= ASKED_TABLE;
    }

    pub fn require_combinations(&mut self, run: u64) {
        if self.ok() {
            let e = self.entry();
            assert!(
                e.combinations != 0 && e.combinations == run,
                "rounds: the round draws a matrix of another number of combinations than its planned error is priced for, or the plan names none"
            );
        }
        self.asked |= ASKED_COMBINATIONS;
    }

    pub fn require_sharing(&mut self, run: u64) {
        if self.ok() {
            let e = self.entry();
            assert!(
                e.sharing != 0 && e.sharing == run,
                "rounds: the round draws a point for another number of requests than its planned error is priced for, or the plan names none"
            );
        }
        self.asked |= ASKED_SHARING;
    }

    /// Whether this chain, or a chain that it follows, drew the list (`drew`).
    pub fn drew(&self, l: &PositionList) -> bool {
        match &l.drawn_by {
            Some(m) => self.marks.iter().any(|k| Rc::ptr_eq(k, m)),
            None => false,
        }
    }

    /// Whether this chain follows `earlier` (`stands_on`).
    pub fn stands_on(&self, earlier: &VerifierRounds<'_, '_, '_>) -> bool {
        if earlier.marks.is_empty() {
            return false;
        }
        self.marks
            .iter()
            .skip(1)
            .any(|m| Rc::ptr_eq(m, &earlier.marks[0]))
    }

    pub fn plan(&self) -> &Planned {
        &self.plan
    }

    /// The chain's run's value (`run`).
    pub fn run(&self) -> &Digest {
        assert!(
            self.has_run,
            "rounds: a chain without random bytes in its first query has no run's value"
        );
        &self.run
    }

    pub fn configuration(&self) -> &Digest {
        &self.configuration
    }

    pub fn queries(&self) -> usize {
        self.closes as usize
    }

    fn ended(&mut self) -> bool {
        if !self.ok() {
            let mut f = self.fate.get();
            f.refused = true;
            self.fate.set(f);
        }
        let mut f = self.fate.get();
        f.ended = true;
        self.fate.set(f);
        self.ok()
    }

    fn follows_a_refusal(&self) -> bool {
        self.earlier_fates.iter().any(|f| f.get().refused)
    }

    fn fail(&mut self, why: &'static str) {
        let mut f = self.fate.get();
        f.refused = true;
        self.fate.set(f);
        if self.why.is_none() {
            self.why = Some(why);
        }
        self.r.refuse();
    }

    fn entry(&self) -> &PlanRound {
        &self.plan.rounds[self.entry.expect("rounds: no round is open")]
    }

    fn item(&mut self, what: Item) {
        if !self.ok() {
            return;
        }
        assert!(!self.sealed, "rounds: the chain has been sealed");
        assert!(!self.lent, "rounds: the chain is lent out");
        self.settle();
        if what == Item::Answer {
            assert!(self.owed > 0, "rounds: an answer that no seed has asked for");
        } else {
            assert!(
                self.owed == 0,
                "rounds: after a round of seeds the prover's message begins with the answers"
            );
        }
        if what == Item::Answer {
            self.owed -= 1;
            self.answers += 1;
        }
        if what == Item::Root {
            assert!(
                self.has_run,
                "rounds: a chain that sends a tree has random bytes in its first query"
            );
            self.roots += 1;
        }
        self.last_was_hiding_sum = what == Item::HidingSum;
    }

    fn take<T: Takeable>(&mut self, x: &mut T) -> bool {
        *x = T::default();
        if !self.ok() {
            return false;
        }
        match T::take_from(self.r) {
            Some(v) => {
                v.append_to(&mut self.message);
                *x = v;
                true
            }
            None => {
                *x = T::default();
                self.fail("a value that the prover sends is missing or not in canonical form");
                false
            }
        }
    }

    fn planned(&mut self, name: &str, kind: RoundKind) -> usize {
        assert!(!self.sealed, "rounds: the chain has been sealed");
        assert!(self.owed == 0, "rounds: a round is closed while answers to a sample are owed");
        self.settle();
        let idx = self.cursor.next_round(name);
        assert!(
            self.plan.rounds[idx].kind == kind,
            "rounds: the round is planned with another kind of verifier message"
        );
        idx
    }

    fn close(&mut self, name: &str, kind: RoundKind, calls: &mut HashCalls) {
        if !self.ok() {
            self.closes += 1;
            self.entry = None;
            return;
        }
        assert!(!self.lent, "rounds: the chain is lent out");
        let idx = self.planned(name, kind);
        let (work_bits, draw_e, draw_nonzero) = {
            let e = &self.plan.rounds[idx];
            (e.work_bits, e.draw_e, e.draw_nonzero)
        };
        assert!(
            kind != RoundKind::Empty || work_bits == 0,
            "rounds: a round in which the verifier says nothing has no work"
        );
        assert!(
            kind == RoundKind::Seed
                || draw_nonzero == 0
                || (kind == RoundKind::Algebraic && draw_nonzero == draw_e),
            "rounds: the elements of a round are all drawn with 0 or, in a round of elements alone, all without"
        );
        self.ask(idx, calls);
    }

    fn ask(&mut self, idx: usize, calls: &mut HashCalls) {
        let (message_bytes, roots, answers, work_bits, kind) = {
            let e = &self.plan.rounds[idx];
            (e.message_bytes, e.roots, e.answers, e.work_bits, e.kind)
        };
        assert!(
            self.message.len() + self.outside == message_bytes
                && self.roots == roots
                && self.answers == answers,
            "rounds: the prover's message has not the planned bytes, roots and answers"
        );
        let p = {
            let mut m = self.chain.as_ref().unwrap().message(calls);
            m.push(&self.message);
            Chain::prefix(&mut m, number_of(kind), work_bits)
        };
        let mut n = 0u64;
        if work_bits > 0 && !self.nonce(&p, work_bits, &mut n) {
            self.fail("a nonce is missing");
        } else if !self
            .chain
            .as_mut()
            .unwrap()
            .step(&p, n, work_bits, calls)
        {
            self.fail("a nonce does not give the proof of work that its round asks for");
        }
        self.message.clear();
        self.roots = 0;
        self.answers = 0;
        self.outside = 0;
        self.last_was_hiding_sum = false;
        self.closes += 1;
        self.entry = Some(idx);
        self.drawn_e = 0;
        self.drawn_nonzero = 0;
        self.drawn_trits = 0;
        self.positions_done = false;
        self.asked = 0;
    }

    fn nonce(&mut self, _p: &ChainPrefix, _work_bits: u32, n: &mut u64) -> bool {
        let bytes = self.plan.set.nonce_bytes as usize;
        match self.r.take(bytes) {
            Some(q) => {
                *n = 0;
                for (i, b) in q.iter().enumerate() {
                    *n |= (*b as u64) << (8 * i);
                }
                true
            }
            None => false,
        }
    }

    fn element(&mut self, nonzero: bool, calls: &mut HashCalls) -> E {
        if !self.ok() {
            return if nonzero { E::one() } else { E::default() };
        }
        assert!(
            self.drawn_e + 1 <= self.entry().draw_e,
            "rounds: more elements are drawn than the round is planned with"
        );
        self.drawn_e += 1;
        if nonzero {
            self.drawn_nonzero += 1;
        }
        if nonzero {
            self.chain.as_mut().unwrap().draw_e_nonzero(calls)
        } else {
            self.chain.as_mut().unwrap().draw_e(calls)
        }
    }

    fn word(&mut self, calls: &mut HashCalls) -> u64 {
        if self.ok() {
            self.chain.as_mut().unwrap().next_word(calls)
        } else {
            0
        }
    }

    fn settle(&mut self) {
        let idx = match self.entry {
            Some(i) => i,
            None => return,
        };
        let (name, draw_e, draw_trits, draw_positions, draw_nonzero, said) = {
            let e = &self.plan.rounds[idx];
            (
                e.name.clone(),
                e.draw_e,
                e.draw_trits,
                e.draw_positions,
                e.draw_nonzero,
                (if e.rows != 0 { ASKED_ROWS } else { 0 })
                    | (if e.first_list != 0 { ASKED_FIRST_LIST } else { 0 })
                    | (if e.group.said { ASKED_GROUP } else { 0 })
                    | (if e.table.said { ASKED_TABLE } else { 0 })
                    | (if e.combinations != 0 { ASKED_COMBINATIONS } else { 0 })
                    | (if e.sharing != 0 { ASKED_SHARING } else { 0 }),
            )
        };
        assert!(
            self.drawn_e == draw_e
                && self.drawn_trits == draw_trits
                && self.positions_done == (draw_positions > 0),
            "rounds: less was drawn than the round is planned with"
        );
        assert!(
            self.drawn_nonzero == draw_nonzero,
            "rounds: another number of elements was drawn without 0 than the round is planned with"
        );
        let unasked = if self.ok() { said & !self.asked } else { 0 };
        assert!(
            unasked == 0,
            "rounds: at the round {}: the plan says beside the round what its error was priced from, and no block has asked for it ({})",
            name,
            unasked
        );
        self.entry = None;
    }

    fn end(&mut self) {
        for f in &self.earlier_fates {
            assert!(
                f.get().ended,
                "rounds: a chain that this one follows has not been brought to its end"
            );
        }
        assert!(!self.lent, "rounds: the chain is lent out");
        assert!(self.owed == 0, "rounds: the protocol ends while answers to a sample are owed");
        self.settle();
        assert!(self.cursor.at_end(), "rounds: the protocol ends before the last planned round");
        assert!(
            self.message.is_empty(),
            "rounds: a prover's message is still open at the chain's end; its round is closed like every other"
        );
    }
}

impl<'a, 'd, 's> Drop for VerifierRounds<'a, 'd, 's> {
    fn drop(&mut self) {
        if !self.ok() {
            let mut f = self.fate.get();
            f.refused = true;
            self.fate.set(f);
        }
        let fate = self.fate.clone();
        self.session.leave(&fate);
    }
}

fn number_of(kind: RoundKind) -> ChainKind {
    match kind {
        RoundKind::Algebraic => ChainKind::Algebraic,
        RoundKind::Epsilon => ChainKind::Epsilon,
        RoundKind::Seed => ChainKind::Seed,
        RoundKind::Positions => ChainKind::Positions,
        RoundKind::Bits => ChainKind::Bits,
        RoundKind::Seal => ChainKind::Seal,
        RoundKind::Empty => ChainKind::Empty,
        RoundKind::Record => panic!("rounds: a round of this kind is no query of the chain"),
    }
}

/// Draws a round's elements of E (`AlgebraicDraw`).
pub struct AlgebraicDraw<'x, 'a, 'd, 's> {
    r: &'x mut VerifierRounds<'a, 'd, 's>,
}

impl AlgebraicDraw<'_, '_, '_, '_> {
    pub fn draw(&mut self, calls: &mut HashCalls) -> E {
        self.r.element(false, calls)
    }
    pub fn draw_nonzero(&mut self, calls: &mut HashCalls) -> E {
        self.r.element(true, calls)
    }
    pub fn require_rows(&mut self, rows: u64) {
        self.r.require_rows(rows);
    }
}

/// Draws the seeds of out-of-domain samples (`SeedDraw`).
pub struct SeedDraw<'x, 'a, 'd, 's> {
    r: &'x mut VerifierRounds<'a, 'd, 's>,
}

impl SeedDraw<'_, '_, '_, '_> {
    /// A seed whose point has `variables` coordinates, for `answers` answers in all (`seed`).
    pub fn seed(&mut self, variables: usize, answers: u32, calls: &mut HashCalls) -> SampleSeed {
        assert!(answers > 0, "rounds: a seed without an answer");
        let (draw_e, draw_nonzero) = (self.r.entry().draw_e, self.r.entry().draw_nonzero);
        assert!(
            !self.r.ok() || (variables as u64 + 1) * draw_nonzero == draw_e,
            "rounds: the seeds of a round have all the planned number of coordinates"
        );
        if self.r.ok() {
            self.r.owed += answers;
        }
        let mut s = SampleSeed::default();
        s.z.reserve(variables);
        for _ in 0..variables {
            s.z.push(self.r.element(false, calls));
        }
        s.beta = self.r.element(true, calls);
        s
    }
}

/// Draws the positions of a round (`PositionsDraw`).
pub struct PositionsDraw<'x, 'a, 'd, 's> {
    r: &'x mut VerifierRounds<'a, 'd, 's>,
}

impl PositionsDraw<'_, '_, '_, '_> {
    /// The planned number of positions below `2^log_n` (`positions`).
    pub fn positions(&mut self, log_n: u32, calls: &mut HashCalls) -> PositionList {
        if !self.r.ok() {
            return PositionList::from_draws(vec![0], log_n);
        }
        let (planned_log_n, draws, matches_run) = {
            let e = self.r.entry();
            (e.log_n, e.draw_positions, !self.r.positions_done && e.draw_positions > 0)
        };
        assert!(
            planned_log_n == log_n,
            "rounds: the round is planned with positions from another range"
        );
        assert!(
            !self.r.positions_done,
            "rounds: the positions of a round are drawn once"
        );
        assert!(
            matches_run,
            "rounds: the round is planned without positions"
        );
        self.r.positions_done = true;
        let mut x = Vec::with_capacity(draws as usize);
        for _ in 0..draws {
            x.push(
                self.r
                    .chain
                    .as_mut()
                    .unwrap()
                    .draw_position(planned_log_n, calls),
            );
        }
        let mut l = PositionList::from_draws(x, planned_log_n);
        l.drawn_by = Some(self.r.marks[0].clone());
        l
    }

    /// The batching element that follows the positions (`batching`).
    pub fn batching(&mut self, calls: &mut HashCalls) -> E {
        assert!(
            !self.r.ok() || self.r.positions_done,
            "rounds: the batching element comes after the positions"
        );
        self.r.element(false, calls)
    }

    pub fn require_rows(&mut self, rows: u64) {
        self.r.require_rows(rows);
    }
    pub fn require_first_list(&mut self, draws: u64) {
        self.r.require_first_list(draws);
    }
    pub fn require_table(&mut self, run: &PricedTable) {
        self.r.require_table(run);
    }
    pub fn require_codes(&mut self, run: &PricedGroup) {
        self.r.require_codes(run);
    }
}

/// Draws the entries of an approximate range check (`BitsDraw`).
pub struct BitsDraw<'x, 'a, 'd, 's> {
    r: &'x mut VerifierRounds<'a, 'd, 's>,
}

impl BitsDraw<'_, '_, '_, '_> {
    /// `n` entries in {-1, 0, 1}, two bits per word (`trits`).
    pub fn trits(&mut self, n: usize, calls: &mut HashCalls) -> Vec<i8> {
        let mut t = vec![0i8; n];
        if !self.r.ok() {
            return t;
        }
        assert!(self.r.drawn_trits == 0, "rounds: the entries of a round are drawn in one call");
        self.r.drawn_trits += n as u64;
        assert!(
            self.r.drawn_trits <= self.r.entry().draw_trits,
            "rounds: more entries are drawn than the round is planned with"
        );
        let mut i = 0usize;
        while i < n {
            let mut w = self.r.word(calls);
            let mut j = 0usize;
            while j < 32 && i + j < n {
                let b0 = (w & 1) as i32;
                let b1 = ((w & (w << 1) & 2) >> 1) as i32;
                t[i + j] = (b0 - 2 * b1) as i8;
                w >>= 2;
                j += 1;
            }
            i += 32;
        }
        t
    }

    /// The round draws a matrix of `run` combinations (`require_combinations`). C++'s
    /// `chainTrits` asks before an entry is drawn.
    pub fn require_combinations(&mut self, run: u64) {
        self.r.require_combinations(run);
    }
}
