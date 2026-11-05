//! The Fiat–Shamir hash chain, ported from `blocks/chain/chain.h`.
//!
//! A chain has one 32-byte value, `rho`. The first query hashes the label, the parameters' digest,
//! the statement, the record, the salted flag and, for a salted chain, the run's value. Each round
//! hashes `rho`, the prover's message, the round number, the kind and the work bits, plus the
//! nonce; the answer's blocks give the next `rho` and the verifier's message. The hash calls are
//! counted in an explicit `HashCalls`, so the core keeps no global state.

use alloc::vec::Vec;

use crate::field::ext::{F, E};
use crate::hash::calls::HashCalls;
use crate::hash::domains::Domain;
use crate::hash::modes::{
    chain_absorb, chain_block, chain_call, run_value, work_test, ChainCall, ChainPrefix, Digest,
    Hasher, Tag,
};
use crate::numbers::real::{DRAW_TRIES, NONZERO_TRIES};

/// The label of a committed table's record seeds (`LABEL_RECORD`).
pub const LABEL_RECORD: u64 = 1u64 << 32;

/// What a round's verifier's message consists of (`ChainKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u64)]
pub enum ChainKind {
    Algebraic = 1,
    Epsilon = 2,
    Seed = 3,
    Positions = 4,
    Bits = 5,
    Seal = 6,
    Empty = 7,
}

/// What is fixed before the prover speaks (`FirstQuery`).
#[derive(Clone, Debug, Default)]
pub struct FirstQuery {
    pub label: u64,
    pub parameters: Digest,
    pub statement: Vec<u8>,
    pub record: Vec<u8>,
    pub salted: bool,
    pub salt_in_proof: bool,
    pub salt: Digest,
}

impl FirstQuery {
    pub fn new(label: u64) -> Self {
        FirstQuery { label, salted: true, salt_in_proof: true, ..FirstQuery::default() }
    }
}

/// The run's value of a salted chain (`first_query_run`).
pub fn first_query_run(q: &FirstQuery, calls: &mut HashCalls) -> Digest {
    run_value(q.label, &q.parameters, &q.salt, calls)
}

/// A source of the words of a verifier's message (`Next`).
pub trait NextWord {
    fn next_word(&mut self) -> u64;
}

/// One element of F by rejection sampling (`draw_F_from`).
pub fn draw_f_from<N: NextWord>(next: &mut N) -> F {
    for _ in 0..DRAW_TRIES {
        if let Some(x) = F::from_word(next.next_word()) {
            return x;
        }
    }
    F::zero()
}

/// One element of E (`draw_E_from`).
pub fn draw_e_from<N: NextWord>(next: &mut N) -> E {
    let mut x = E::default();
    for i in 0..3 {
        x.0[i] = draw_f_from(next);
    }
    x
}

/// The fast path for the first element of a verifier's message (`draw_E_straight`).
pub fn draw_e_straight(w0: u64, w1: u64, w2: u64, nonzero: bool, out: &mut E) -> bool {
    let a = F::from_word(w0);
    let b = F::from_word(w1);
    let c = F::from_word(w2);
    let (a, b, c) = match (a, b, c) {
        (Some(a), Some(b), Some(c)) => (a, b, c),
        _ => return false,
    };
    let x = E([a, b, c]);
    if nonzero && x == E::default() {
        return false;
    }
    *out = x;
    true
}

/// A nonzero element of E (`draw_E_nonzero_from`).
pub fn draw_e_nonzero_from<N: NextWord>(next: &mut N) -> E {
    for _ in 0..NONZERO_TRIES {
        let x = draw_e_from(next);
        if x != E::default() {
            return x;
        }
    }
    E::one()
}

const NO_CHAIN: u64 = u64::MAX;
const SHUT: u8 = 0xFF;

/// The chain (`ChainT<HashFn>`). A default-constructed chain is only a target of assignment; a
/// round or draw on it is a caller's mistake and panics.
#[derive(Clone, Debug)]
pub struct Chain {
    rho: Digest,
    rounds: u64,
    label: u64,
    query: ChainPrefix,
    nonce: u64,
    call: u64,
    word: [u64; 8],
    next: u8,
    have: u8,
}

impl Default for Chain {
    fn default() -> Self {
        Chain {
            rho: Digest::zero(),
            rounds: NO_CHAIN,
            label: 0,
            query: ChainPrefix::default(),
            nonce: 0,
            call: 0,
            word: [0; 8],
            next: 0,
            have: 0,
        }
    }
}

impl Chain {
    /// The chain of a first query. `HashCalls` receives the first query's compressions.
    pub fn new(q: &FirstQuery, calls: &mut HashCalls) -> Self {
        assert!(q.label >> 48 == 0, "chain: a label is below 2^48");
        let run = if q.salted { Some(first_query_run(q, calls)) } else { None };
        let mut h = Hasher::new(&Tag::plain(Domain::ChainStart, 0), q.label, calls);
        h.push_digest(&q.parameters);
        h.push_u64(q.statement.len() as u64);
        h.push(&q.statement);
        h.push_u64(q.record.len() as u64);
        h.push(&q.record);
        h.push_u64(q.salted as u64);
        if let Some(run) = run {
            h.push_digest(&run);
        }
        let rho = h.finish();
        Chain { rho, rounds: 0, label: q.label, ..Chain::default() }
    }

    /// Starts the next round's query; the caller pushes the prover's message (`message`).
    pub fn message<'a>(&self, calls: &'a mut HashCalls) -> Hasher<'a> {
        assert!(self.rounds != NO_CHAIN, "chain: a chain that was made from no first query");
        chain_absorb(&self.rho, self.rounds + 1, self.label, calls)
    }

    /// Ends the message and returns the entire query except its nonce (`prefix`).
    pub fn prefix(message: &mut Hasher<'_>, kind: ChainKind, work_bits: u32) -> ChainPrefix {
        assert!(work_bits < 256, "chain: a round's work bits have one byte of the query's last word");
        message.push_u64(kind as u64 | (work_bits as u64) << 8);
        message.before_nonce()
    }

    /// Makes the round's query and tests its proof of work (`step`).
    pub fn step(&mut self, p: &ChainPrefix, nonce: u64, work_bits: u32, calls: &mut HashCalls) -> bool {
        assert!(work_bits > 0 || nonce == 0, "chain: a round without work has no nonce");
        let first = chain_call(p, nonce, 0, calls);
        if !Self::has_work(&first, work_bits) {
            return false;
        }
        self.take(p, nonce, work_bits, &first);
        true
    }

    /// The work test, on call 0 of a query (`has_work`).
    pub fn has_work(first: &ChainCall, work_bits: u32) -> bool {
        work_test(first.w[0], work_bits)
    }

    /// `prefix()` and `step()` in one, for a round without work (`close`).
    pub fn close(&mut self, message: &mut Hasher<'_>, kind: ChainKind, calls: &mut HashCalls) {
        let p = Self::prefix(message, kind, 0);
        self.step(&p, 0, 0, calls);
    }

    /// An entire round without work whose message is exactly `words` (`round`).
    pub fn round(&mut self, words: &[u64], kind: ChainKind, calls: &mut HashCalls) {
        let mut m = self.message(calls);
        for &w in words {
            m.push_u64(w);
        }
        let p = Self::prefix(&mut m, kind, 0);
        self.step(&p, 0, 0, calls);
    }

    /// A round with an empty message (`round`).
    pub fn round_empty(&mut self, kind: ChainKind, calls: &mut HashCalls) {
        let mut m = self.message(calls);
        let p = Self::prefix(&mut m, kind, 0);
        self.step(&p, 0, 0, calls);
    }

    /// Advances the chain to a value that the caller computed (`take_shut`).
    pub fn take_shut(&mut self, value: &Digest) {
        self.rho = *value;
        self.rounds = self.next_round();
        self.shut();
    }

    /// Ends the current verifier's message (`shut`).
    pub fn shut(&mut self) {
        self.next = 0;
        self.have = SHUT;
    }

    pub fn rounds(&self) -> u64 {
        self.rounds
    }
    pub fn label(&self) -> u64 {
        self.label
    }
    pub fn value(&self) -> &Digest {
        &self.rho
    }

    /// The next word of the verifier's message (`next_word`).
    pub fn next_word(&mut self, calls: &mut HashCalls) -> u64 {
        assert!(
            self.rounds > 0 && self.rounds != NO_CHAIN,
            "chain: a draw before the first round"
        );
        assert!(
            self.have != SHUT,
            "chain: this copy's verifier message is over; it draws again after its next round"
        );
        if self.next == self.have {
            let c = chain_call(&self.query, self.nonce, self.call, calls);
            self.call += 1;
            self.word = c.w;
            self.next = 0;
            self.have = 8;
        }
        let w = self.word[self.next as usize];
        self.next += 1;
        w
    }

    pub fn draw_f(&mut self, calls: &mut HashCalls) -> F {
        let mut row = Row { chain: self, calls };
        draw_f_from(&mut row)
    }

    pub fn draw_e(&mut self, calls: &mut HashCalls) -> E {
        let mut row = Row { chain: self, calls };
        draw_e_from(&mut row)
    }

    pub fn draw_e_nonzero(&mut self, calls: &mut HashCalls) -> E {
        let mut row = Row { chain: self, calls };
        draw_e_nonzero_from(&mut row)
    }

    pub fn draw_position(&mut self, log_n: u32, calls: &mut HashCalls) -> u64 {
        assert!(log_n < 64, "chain: positions lie below 2^63");
        self.next_word(calls) & ((1u64 << log_n) - 1)
    }

    fn next_round(&self) -> u64 {
        assert!(
            self.rounds != NO_CHAIN,
            "chain: a chain that was made from no first query and is no copy of one"
        );
        self.rounds + 1
    }

    /// Advances the chain by one round, given the query and its hash call 0 (`take`).
    fn take(&mut self, p: &ChainPrefix, nonce: u64, work_bits: u32, first: &ChainCall) {
        self.rho = chain_block(first, if work_bits > 0 { 1 } else { 0 });
        self.rounds = self.next_round();
        self.query = *p;
        self.nonce = nonce;
        self.call = 1;
        self.next = 0;
        self.have = 0;
        if work_bits == 0 {
            for i in 0..4 {
                self.word[i] = first.w[4 + i];
            }
            self.have = 4;
        }
    }
}

struct Row<'a, 'b> {
    chain: &'a mut Chain,
    calls: &'b mut HashCalls,
}

impl NextWord for Row<'_, '_> {
    fn next_word(&mut self) -> u64 {
        self.chain.next_word(self.calls)
    }
}
