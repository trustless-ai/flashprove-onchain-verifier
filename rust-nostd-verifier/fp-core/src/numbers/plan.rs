//! The plan of one protocol run and its verdict, ported from `blocks/numbers/plan.h`.
//!
//! S2a ports the data model and the verdict needed by the error accounting. The planners of
//! `blocks/numbers/blocks.h`, which append rounds from shapes, arrive with the proof-system shapes
//! in S2b. A `Planned` here is built from a C++ dump or, later, by the ported planners.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

use super::real::{
    bits_of, Big, Bound, Dir, Real, DRAW_TRIES, NONZERO_TRIES,
};
use super::round_names::*;
use super::setting::{CountSource, ErrorKind, RoundKind, Scope, Setting};

/// The kind that belongs to a round's name (`kind_of_round`, plan.h:43-58). Returns `None` for a
/// name outside the format; `configure` rejects plans that contain one.
pub fn kind_of_round(name: &str) -> Option<RoundKind> {
    const ALL: &[(&str, RoundKind)] = &[
        (R_SEND_SEED, RoundKind::Seed),
        (R_SEND_ANSWER, RoundKind::Empty),
        (R_BAT, RoundKind::Algebraic),
        (R_BAT_SIGMA, RoundKind::Algebraic),
        (R_SPLIT, RoundKind::Empty),
        (R_PSC_EPSILON, RoundKind::Epsilon),
        (R_PSC_ROUND, RoundKind::Algebraic),
        (R_PSC_Y, RoundKind::Algebraic),
        (R_PSC_VALUES, RoundKind::Empty),
        (R_ZERO, RoundKind::Algebraic),
        (R_LINE, RoundKind::Algebraic),
        (R_LKP_SHIFT, RoundKind::Algebraic),
        (R_JOIN, RoundKind::Algebraic),
        (R_LKP, RoundKind::Algebraic),
        (R_RNG, RoundKind::Bits),
        (R_FOLD_EPSILON, RoundKind::Epsilon),
        (R_FOLD_ROUND, RoundKind::Algebraic),
        (R_LOC, RoundKind::Positions),
        (R_CS, RoundKind::Positions),
        (R_BASE_LAMBDA, RoundKind::Algebraic),
        (R_BASE, RoundKind::Positions),
        (R_SEAL, RoundKind::Seal),
        (R_LAST, RoundKind::Empty),
        (R_REPLY, RoundKind::Empty),
        (R_RECORD, RoundKind::Record),
        (R_LIN_POINT, RoundKind::Algebraic),
        (R_LIN_ZETA, RoundKind::Algebraic),
        (R_LINK_POINT, RoundKind::Algebraic),
        (R_LINK, RoundKind::Positions),
        (R_LINK_PHI, RoundKind::Algebraic),
    ];
    ALL.iter().find(|(n, _)| *n == name).map(|(_, k)| *k)
}

/// What a round's error bound was computed from (`Priced`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Priced {
    Nothing,
    SettingAlone,
    TheRoundItself,
    AsSaid,
    OnTheCallersWord,
}

/// Why a plan does not hold (`Cause`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cause {
    None,
    Refused,
    AboveTheTarget,
    Word,
    TwoDistances,
}

/// The kind of a planned message (`MessageKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MessageKind {
    Scalars,
    Answers,
    Root,
    Nonce,
    Columns,
    Salts,
    Paths,
    Head,
}

/// Which test on the committed table a round belongs to (`TableTest`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableTest {
    Later,
    OneTime,
    Link,
}

/// The public numbers of one code in a group (`PricedCode`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PricedCode {
    pub log_n: u32,
    pub ell: u64,
    pub r: u64,
}

/// A group's stated public numbers and analysis choice (`PricedGroup`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PricedGroup {
    pub main: PricedCode,
    pub mask: PricedCode,
    pub k: u32,
    pub h: u32,
    pub slots: u64,
    pub said: bool,
    pub rule: u32,
    pub m: u64,
}

impl Default for PricedGroup {
    fn default() -> Self {
        PricedGroup {
            main: PricedCode::default(),
            mask: PricedCode::default(),
            k: 0,
            h: 0,
            slots: 1,
            said: false,
            rule: 0,
            m: 0,
        }
    }
}

impl PricedCode {
    /// All the fields are compared (`PricedCode::operator==`).
    pub fn same(&self, o: &PricedCode) -> bool {
        self.log_n == o.log_n && self.ell == o.ell && self.r == o.r
    }
}

impl PricedGroup {
    /// All but `said`, `rule` and `m`: what a run can be compared with
    /// (`PricedGroup::operator==`).
    pub fn same_run(&self, o: &PricedGroup) -> bool {
        self.main.same(&o.main)
            && self.mask.same(&o.mask)
            && self.k == o.k
            && self.h == o.h
            && self.slots == o.slots
    }
}

/// The committed table's distances (`TableDistances`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TableDistances {
    pub radius: u64,
    pub later_radius: u64,
    pub m_once: u64,
    pub m_later: u64,
}

/// A committed table's stated numbers (`PricedTable`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PricedTable {
    pub code: PricedCode,
    pub v: u32,
    pub answers: u32,
    pub distances: TableDistances,
    pub said: bool,
    pub test: TableTest,
}

impl Default for PricedTable {
    fn default() -> Self {
        PricedTable {
            code: PricedCode::default(),
            v: 0,
            answers: 0,
            distances: TableDistances::default(),
            said: false,
            test: TableTest::Later,
        }
    }
}

impl PricedTable {
    /// All but `said` (`PricedTable::operator==`).
    pub fn same_run(&self, o: &PricedTable) -> bool {
        self.code.same(&o.code)
            && self.v == o.v
            && self.answers == o.answers
            && self.distances == o.distances
            && self.test == o.test
    }
}

/// One round (`PlanRound`).
#[derive(Clone, Debug)]
pub struct PlanRound {
    pub name: String,
    pub where_: String,
    pub kind: RoundKind,
    pub why: ErrorKind,
    pub scope: Scope,
    pub error: Real,
    pub rests: CountSource,
    pub work_bits: u32,
    pub count: u64,
    pub part: u32,
    pub message_bytes: usize,
    pub roots: u32,
    pub answers: u32,
    pub draw_e: u64,
    pub draw_nonzero: u64,
    pub draw_positions: u64,
    pub log_n: u32,
    pub draw_trits: u64,
    pub rows: u64,
    pub first_list: u64,
    pub group: PricedGroup,
    pub table: PricedTable,
    pub combinations: u64,
    pub sharing: u64,
    pub priced: Priced,
}

impl Default for PlanRound {
    fn default() -> Self {
        PlanRound {
            name: String::new(),
            where_: String::new(),
            kind: RoundKind::Empty,
            why: ErrorKind::Zero,
            scope: Scope::Request,
            error: Real::default(),
            rests: CountSource::Johnson,
            work_bits: 0,
            count: 1,
            part: 0,
            message_bytes: 0,
            roots: 0,
            answers: 0,
            draw_e: 0,
            draw_nonzero: 0,
            draw_positions: 0,
            log_n: 0,
            draw_trits: 0,
            rows: 0,
            first_list: 0,
            group: PricedGroup::default(),
            table: PricedTable::default(),
            combinations: 0,
            sharing: 0,
            priced: Priced::Nothing,
        }
    }
}

impl PlanRound {
    pub fn says(&self) -> bool {
        self.rows != 0
            || self.first_list != 0
            || self.group.said
            || self.table.said
            || self.combinations != 0
            || self.sharing != 0
    }

    /// Null, or how `priced` contradicts the rest of the round (`word_fault`).
    pub fn word_fault(&self) -> Option<&'static str> {
        if (self.draw_positions != 0 || self.draw_trits != 0)
            && self.error.zero()
            && self.priced != Priced::OnTheCallersWord
        {
            return Some("a round that draws positions or a matrix is priced at 0, which only a round marked ON_THE_CALLERS_WORD may be");
        }
        if self.priced == Priced::Nothing && !self.error.zero() {
            return Some("a round with an error is said to be priced from nothing");
        }
        if (self.priced == Priced::SettingAlone || self.priced == Priced::TheRoundItself)
            && self.says()
        {
            return Some("a round that is priced from the setting or from its own fields says something beside them");
        }
        if self.priced == Priced::AsSaid && !self.says() {
            return Some("a round that is priced from what the plan says beside it says nothing");
        }
        None
    }
}

/// The most 64-bit words of the chain's answer (`most_words`).
pub fn most_words(r: &PlanRound, degree: u32) -> u64 {
    DRAW_TRIES as u64
        * degree as u64
        * (r.draw_e + (NONZERO_TRIES as u64 - 1) * r.draw_nonzero)
        + r.draw_positions
        + (r.draw_trits + 31) / 32
        + if r.kind == RoundKind::Seal { 4 } else { 0 }
}

/// One run of bytes in a planned file (`PlanMessage`).
#[derive(Clone, Debug)]
pub struct PlanMessage {
    pub name: String,
    pub where_: String,
    pub kind: MessageKind,
    pub bytes: u64,
    pub expected: f64,
    pub count: u64,
    pub part: u32,
    pub in_chain: bool,
    pub hash_calls: u64,
}

impl Default for PlanMessage {
    fn default() -> Self {
        PlanMessage {
            name: String::new(),
            where_: String::new(),
            kind: MessageKind::Scalars,
            bytes: 0,
            expected: 0.0,
            count: 1,
            part: 0,
            in_chain: false,
            hash_calls: 0,
        }
    }
}

/// A finished plan and its verdict (`Planned`).
#[derive(Clone, Debug)]
pub struct Planned {
    pub set: Setting,
    pub rounds: Vec<PlanRound>,
    pub messages: Vec<PlanMessage>,
    pub parts: Vec<String>,
    pub cause: Cause,
    pub why_not: String,
}

impl Default for Planned {
    fn default() -> Self {
        Planned {
            set: Setting::default(),
            rounds: Vec::new(),
            messages: Vec::new(),
            parts: Vec::new(),
            cause: Cause::Refused,
            why_not: String::from("nothing was planned"),
        }
    }
}

impl Planned {
    pub fn new(
        set: Setting,
        rounds: Vec<PlanRound>,
        messages: Vec<PlanMessage>,
        parts: Vec<String>,
        refused: String,
    ) -> Self {
        let mut p = Planned {
            set,
            rounds,
            messages,
            parts,
            cause: Cause::None,
            why_not: String::new(),
        };
        let (cause, why) = p.judged(&refused);
        p.cause = cause;
        p.why_not = why;
        p
    }

    pub fn holds(&self) -> bool {
        self.cause == Cause::None
    }
    pub fn refused(&self) -> bool {
        self.cause == Cause::Refused
    }
    pub fn cause(&self) -> Cause {
        self.cause
    }
    pub fn why_not(&self) -> &str {
        &self.why_not
    }
    pub fn rounds_sum(&self) -> u64 {
        self.rounds.iter().map(|r| r.count).sum()
    }
    pub fn queries(&self) -> u64 {
        self.rounds_sum()
    }
    pub fn size_of(&self, part: u32) -> (u64, f64) {
        let mut bytes = 0u64;
        let mut expected = 0.0f64;
        for m in &self.messages {
            if m.part == part {
                bytes += m.bytes * m.count;
                expected += m.expected * m.count as f64;
            }
        }
        (bytes, expected)
    }
    pub fn part_index(&self, name: &str) -> Option<usize> {
        self.parts.iter().position(|p| p == name)
    }

    /// True if every round has one of the format's names, and so that name's kind
    /// (`Planned::names_of_the_format`, plan.h:343-348).
    pub fn names_of_the_format(&self) -> bool {
        self.rounds.iter().all(|r| kind_of_round(&r.name).is_some())
    }

    /// An upper bound on the chance that a draw of one E element reaches its cap (`capped`).
    pub fn capped(&self) -> Real {
        let mut bits = 0usize;
        while Big::cmp(&Big::two_to(bits), &self.set.p) == Ordering::Less {
            bits += 1;
        }
        let num = Big::sub(&Big::two_to(bits), &self.set.p);
        let den = Big::two_to(bits);
        let ratio = Bound::ratio(&num, &den);
        (Bound::from_u64(self.set.degree as u64) * Bound::pow(&ratio, DRAW_TRIES as u64))
            .error()
    }

    /// The round's error with the distance of its draws from uniform (`whole_error`).
    pub fn whole_error(&self, r: &PlanRound, unit: &Real) -> Real {
        if r.draw_e == 0 {
            return r.error.clone();
        }
        let n = Real::from_u64(r.draw_e + (NONZERO_TRIES as u64 - 1) * r.draw_nonzero);
        let mut e = Real::add(
            &r.error,
            &Real::mul(unit, &n, Dir::Up),
            Dir::Up,
        );
        if r.draw_nonzero != 0 {
            let card = self.set.card_e();
            let denom = Bound::pow(&Bound::from_big(&card), NONZERO_TRIES as u64);
            let term = (Bound::from_u64(1) / denom).error();
            e = Real::add(
                &e,
                &Real::mul(&term, &Real::from_u64(r.draw_nonzero), Dir::Up),
                Dir::Up,
            );
        }
        e
    }

    /// Does the round hold at the target, work counted? (`holds`).
    pub fn holds_round(&self, r: &PlanRound, unit: &Real) -> bool {
        let goal = Real::two_to(r.work_bits as i64 - self.set.target as i64);
        Real::cmp(&self.whole_error(r, unit), &goal) != Ordering::Greater
    }

    pub fn holds_round_default(&self, r: &PlanRound) -> bool {
        let unit = self.capped();
        self.holds_round(r, &unit)
    }

    fn at(i: usize, r: &PlanRound) -> String {
        alloc::format!(
            "round {}, {}{}: ",
            i + 1,
            r.name,
            if r.where_.is_empty() {
                String::new()
            } else {
                alloc::format!(", {}", r.where_)
            }
        )
    }

    fn judged(&self, refused: &str) -> (Cause, String) {
        if !refused.is_empty() {
            return (Cause::Refused, String::from(refused));
        }
        let unit = self.capped();
        for (i, r) in self.rounds.iter().enumerate() {
            if !self.holds_round(r, &unit) {
                return (
                    Cause::AboveTheTarget,
                    Self::at(i, r) + "the error is above the target, work counted",
                );
            }
            if let Some(fault) = r.word_fault() {
                return (Cause::Word, Self::at(i, r) + fault);
            }
        }
        let mut chosen: BTreeMap<[u64; 6], (u32, u64)> = BTreeMap::new();
        for (i, r) in self.rounds.iter().enumerate() {
            let g = &r.group;
            if !g.said {
                continue;
            }
            let key = [
                g.main.log_n as u64,
                g.main.ell,
                g.main.r,
                g.mask.log_n as u64,
                g.mask.ell,
                g.mask.r,
            ];
            let choice = (g.rule, g.m);
            if let Some(old) = chosen.get(&key) {
                if *old != choice {
                    return (
                        Cause::TwoDistances,
                        Self::at(i, r)
                            + "priced at another distance than an earlier round on the same two codes",
                    );
                }
            } else {
                chosen.insert(key, choice);
            }
        }
        (Cause::None, String::new())
    }
}

/// Steps through those rounds of a plan without repeats that are queries of the hash chain
/// (`Cursor`).
pub struct Cursor {
    plan: Rc<Planned>,
    at: usize,
}

impl Cursor {
    /// Ends the process unless the plan holds and was computed over this build's field.
    pub fn new(plan: Rc<Planned>) -> Self {
        assert!(
            plan.holds(),
            "Cursor: the parameters are not admitted: {}",
            plan.why_not()
        );
        let build = Setting::of_this_build();
        assert!(
            plan.set.circle == build.circle
                && Big::cmp(&plan.set.p, &build.p) == Ordering::Equal
                && plan.set.degree == build.degree,
            "Cursor: the plan's errors were reckoned over another field than this build's"
        );
        Cursor { plan, at: 0 }
    }

    /// The next round that is a query of the hash chain; the process ends if its name differs.
    /// Returns the round's index.
    pub fn next_round(&mut self, name: &str) -> usize {
        self.skip();
        assert!(
            self.at < self.plan.rounds.len(),
            "Cursor: a round is run after the last planned one"
        );
        let r = &self.plan.rounds[self.at];
        assert!(r.count == 1, "Cursor: a plan with repeats cannot be run");
        assert!(
            r.name == name,
            "Cursor: the round that is run is not the next planned one"
        );
        let at = self.at;
        self.at += 1;
        at
    }

    pub fn at_end(&mut self) -> bool {
        self.skip();
        self.at == self.plan.rounds.len()
    }

    pub fn plan(&self) -> &Planned {
        &self.plan
    }

    fn skip(&mut self) {
        while self.at < self.plan.rounds.len()
            && self.plan.rounds[self.at].kind == RoundKind::Record
        {
            self.at += 1;
        }
    }
}

/// The mutable plan that the planners write into (`Plan`, plan.h:447-625). `Plan::finish` makes a
/// read-only `Planned` of it; whatever runs, checks or prints a plan takes a `Planned`.
pub struct Plan {
    /// The error bounds read it. A `Plan` can be copied but not assigned in C++; in Rust it is
    /// plain data and can be replaced, which no planner does.
    pub set: Setting,
    /// A planning call at full size: blocks may enter equal rounds once, with a count.
    pub compact: bool,
    rounds_: Vec<PlanRound>,
    messages_: Vec<PlanMessage>,
    parts_: Vec<String>,
    /// The numbers of the trees that may be opened at one list alone and have been (`OneList`,
    /// blocks.h:282; `plan_open`). Read and written by the planner pass.
    one_list_opened_: BTreeSet<u64>,
    refused_: String,
    repeat_: Vec<u64>,
    times_: u64,
    part_: u32,
    scope_: Scope,
    open_bytes_: usize,
    open_roots_: u32,
    open_answers_: u32,
}

impl Plan {
    /// A plan whose first part is `"proof"` (`Plan(const Setting&, const std::string& = "proof")`,
    /// plan.h:449).
    pub fn new(set: Setting) -> Self {
        Plan::with_first_part(set, "proof")
    }

    /// A plan whose first part is `first_part` (plan.h:449).
    pub fn with_first_part(set: Setting, first_part: &str) -> Self {
        Plan {
            set,
            compact: false,
            rounds_: Vec::new(),
            messages_: Vec::new(),
            parts_: vec![String::from(first_part)],
            one_list_opened_: BTreeSet::new(),
            refused_: String::new(),
            repeat_: Vec::new(),
            times_: 1,
            part_: 0,
            scope_: Scope::Request,
            open_bytes_: 0,
            open_roots_: 0,
            open_answers_: 0,
        }
    }

    /// The only way from a `Plan` to a `Planned` (`Plan::finish`, plan.h:455-460). Rounds and
    /// messages are copied: nothing that can still write this plan reaches the `Planned`.
    pub fn finish(&self) -> Rc<Planned> {
        let mut refused = self.refused_.clone();
        if refused.is_empty() && (self.open_bytes_ != 0 || self.open_roots_ != 0 || self.open_answers_ != 0) {
            refused = String::from("the plan ends in the middle of a prover's message: no round takes it in");
        }
        if refused.is_empty() && !self.repeat_.is_empty() {
            refused = String::from("the plan ends inside a repeat");
        }
        Rc::new(Planned::new(
            self.set.clone(),
            self.rounds_.clone(),
            self.messages_.clone(),
            self.parts_.clone(),
            refused,
        ))
    }

    /// Rejects the plan; the first reason is kept (`Plan::refuse`, plan.h:466-468). An empty
    /// reason rejects too.
    pub fn refuse(&mut self, why: &str) {
        if self.refused_.is_empty() {
            self.refused_ = if why.is_empty() {
                String::from("refused, and the caller gave no reason")
            } else {
                String::from(why)
            };
        }
    }

    pub fn refused(&self) -> bool {
        !self.refused_.is_empty()
    }

    /// The first refusal reason; empty if none (`Plan::why`, plan.h:470).
    pub fn why(&self) -> &str {
        &self.refused_
    }

    /// What follows belongs to this file or part of one (`begin_part`, plan.h:477-481).
    pub fn begin_part(&mut self, name: &str) {
        for (i, p) in self.parts_.iter().enumerate() {
            if p == name {
                self.part_ = i as u32;
                return;
            }
        }
        self.parts_.push(String::from(name));
        self.part_ = (self.parts_.len() - 1) as u32;
    }

    pub fn begin_scope(&mut self, s: Scope) {
        self.scope_ = s;
    }

    pub fn scope(&self) -> Scope {
        self.scope_
    }

    /// What is added between this and `pop_repeat()` is entered once, with count `n`; nested
    /// repeats multiply (`push_repeat`, plan.h:484-489). A repeat of 0, or one that would pass
    /// 2^64, rejects the plan.
    pub fn push_repeat(&mut self, n: u64) {
        let mut n = n;
        if n == 0 {
            self.refuse("a repeat of 0 times");
            n = 1;
        }
        if self.times_ > u64::MAX / n {
            self.refuse("repeats of 2^64 times or more");
            n = 1;
        }
        self.repeat_.push(n);
        self.times_ *= n;
    }

    pub fn pop_repeat(&mut self) {
        assert!(!self.repeat_.is_empty(), "Plan: pop_repeat without push_repeat");
        self.times_ /= *self.repeat_.last().unwrap();
        self.repeat_.pop();
    }

    pub fn times(&self) -> u64 {
        self.times_
    }

    /// The numbers that have been opened at one list alone (`Plan::one_list_opened_`, plan.h:617).
    pub fn one_list_opened_mut(&mut self) -> &mut BTreeSet<u64> {
        &mut self.one_list_opened_
    }

    /// As many names as a `Setting` has fields, so that a new field stops the build here
    /// (`Plan::same_setting`, plan.h:497-507).
    pub fn same_setting(a: &Setting, b: &Setting) -> bool {
        if a.work != b.work {
            return false;
        }
        a.field_name == b.field_name
            && Big::cmp(&a.p, &b.p) == Ordering::Equal
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
    }

    /// The prover sends `n` elements of E (`send_scalars`, plan.h:524-526).
    pub fn send_scalars(&mut self, name: &str, n: u64) {
        if n != 0 {
            self.chain_message(name, MessageKind::Scalars, n * self.set.e_bytes as u64);
        }
    }

    /// The prover sends `n` sample answers (`send_answers`, plan.h:527-531).
    pub fn send_answers(&mut self, name: &str, n: u64) {
        if n == 0 {
            return;
        }
        self.chain_message(name, MessageKind::Answers, n * self.set.e_bytes as u64);
        self.open_answers_ = self.open_answers_.wrapping_add(n as u32);
    }

    /// The prover sends a root (`send_root`, plan.h:532-535).
    pub fn send_root(&mut self, name: &str) {
        self.chain_message(name, MessageKind::Root, self.set.digest_bytes as u64);
        self.open_roots_ = self.open_roots_.wrapping_add(1);
    }

    /// Bytes of the file that do not enter the chain (`file`, plan.h:537-543).
    pub(crate) fn file(&mut self, name: &str, kind: MessageKind, bytes: u64, expected: f64, hash_calls: u64) {
        if bytes == 0 {
            return;
        }
        self.messages_.push(PlanMessage {
            name: String::from(name),
            where_: String::new(),
            kind,
            bytes,
            expected,
            count: self.times_,
            part: self.part_,
            in_chain: false,
            hash_calls,
        });
    }

    /// Labels the message that was added last with its place in the protocol (`last_message_at`,
    /// plan.h:545).
    pub fn last_message_at(&mut self, where_: &str) {
        if let Some(m) = self.messages_.last_mut() {
            m.where_ = String::from(where_);
        }
    }

    /// A round with an empty verifier's message (`close_none`, plan.h:548-557). A root in the
    /// prover's message rejects the plan.
    pub fn close_none(&mut self, name: &str, where_: &str) -> &mut PlanRound {
        let mut r = PlanRound::default();
        r.name = String::from(name);
        r.where_ = String::from(where_);
        r.scope = self.scope_;
        r.count = self.times_;
        r.part = self.part_;
        if self.open_roots_ != 0 {
            self.refuse(&alloc::format!(
                "round {}: a root stands in the query of the next verifier's message that is not empty",
                name
            ));
        }
        r.message_bytes = self.open_bytes_;
        r.answers = self.open_answers_;
        self.open_bytes_ = 0;
        self.open_answers_ = 0;
        Self::require_kind(&r);
        self.rounds_.push(r);
        self.rounds_.last_mut().unwrap()
    }

    /// A round with a verifier's message (`close`, plan.h:561-578). `r` holds what the round draws
    /// and states; the other fields are set here, `work_bits` from the setting by `why` and the
    /// scope. Returns `work_bits`.
    pub fn close(
        &mut self,
        name: &str,
        kind: RoundKind,
        why: ErrorKind,
        error: &Bound,
        priced: Priced,
        mut r: PlanRound,
    ) -> u32 {
        assert!(
            kind != RoundKind::Empty,
            "Plan: close() is for a verifier's message that is not empty"
        );
        if error.bad {
            self.refuse(&alloc::format!("round {}: a formula was asked outside its range", name));
        }
        r.name = String::from(name);
        r.kind = kind;
        r.why = why;
        r.scope = self.scope_;
        r.count = self.times_;
        r.part = self.part_;
        r.error = error.error();
        r.priced = priced;
        r.work_bits = self.set.work_of(why, self.scope_);
        assert!(
            kind != RoundKind::Seal || r.work_bits == 0,
            "Plan: a seal bears no proof of work"
        );
        // Six bits of room: an honest search then leaves the nonce's range with probability e^-64.
        if r.work_bits >= self.set.target
            || (r.work_bits != 0 && r.work_bits as u64 + 6 > 8 * self.set.nonce_bytes as u64)
        {
            self.refuse(&alloc::format!(
                "round {}: more work bits than the target or the nonce has room for",
                name
            ));
        }
        r.message_bytes = self.open_bytes_;
        r.roots = self.open_roots_;
        r.answers = self.open_answers_;
        self.open_bytes_ = 0;
        self.open_roots_ = 0;
        self.open_answers_ = 0;
        if r.work_bits != 0 {
            self.file(
                "nonce",
                MessageKind::Nonce,
                self.set.nonce_bytes as u64,
                self.set.nonce_bytes as f64,
                0,
            );
        }
        Self::require_kind(&r);
        let work_bits = r.work_bits;
        self.rounds_.push(r);
        work_bits
    }

    /// Adds an otherwise empty round that the caller fills in (`close`, plan.h:580-583, the
    /// hand-made-plan overload).
    pub fn close_handmade(
        &mut self,
        name: &str,
        kind: RoundKind,
        why: ErrorKind,
        error: &Bound,
        priced: Priced,
    ) -> &mut PlanRound {
        self.close(name, kind, why, error, priced, PlanRound::default());
        self.rounds_.last_mut().unwrap()
    }

    /// Adds a round that its planner filled itself: no query of this chain (`enter`, plan.h:585-589).
    pub fn enter(&mut self, mut r: PlanRound) {
        r.part = self.part_;
        Self::require_kind(&r);
        self.rounds_.push(r);
    }

    /// Appends the rounds and messages of a finished plan under the present part and repeat
    /// (`append`, plan.h:592-602).
    pub fn append(&mut self, o: &Planned) {
        assert!(
            self.open_bytes_ == 0,
            "Plan: append in the middle of a prover's message"
        );
        if o.cause() == Cause::Refused {
            self.refuse(o.why_not());
        }
        if !Plan::same_setting(&self.set, &o.set) {
            self.refuse("rounds that were priced under another setting are appended");
        }
        for r in &o.rounds {
            if r.count > u64::MAX / self.times_ {
                self.refuse("repeats of 2^64 times or more");
            }
        }
        for m in &o.messages {
            if m.count > u64::MAX / self.times_ {
                self.refuse("repeats of 2^64 times or more");
            }
        }
        let part = self.part_;
        let times = self.times_;
        for r in &o.rounds {
            let mut r = r.clone();
            r.part = part;
            // C++ unsigned multiplication wraps; a product that passed the checks above is exact.
            r.count = r.count.wrapping_mul(times);
            self.rounds_.push(r);
        }
        for m in &o.messages {
            let mut m = m.clone();
            m.part = part;
            m.count = m.count.wrapping_mul(times);
            self.messages_.push(m);
        }
    }

    /// A round of the format is planned with its name's kind (`require_kind`, plan.h:603-606).
    fn require_kind(r: &PlanRound) {
        assert!(
            kind_of_round(&r.name).map_or(true, |kind| kind == r.kind),
            "Plan: a round of the format is planned with another kind than its name's"
        );
    }

    /// Bytes of the prover's message that enter the chain (`chain_message`, plan.h:607-613).
    fn chain_message(&mut self, name: &str, kind: MessageKind, bytes: u64) {
        self.messages_.push(PlanMessage {
            name: String::from(name),
            where_: String::new(),
            kind,
            bytes,
            expected: bytes as f64,
            count: self.times_,
            part: self.part_,
            in_chain: true,
            hash_calls: 0,
        });
        self.open_bytes_ += bytes as usize;
    }
}

/// A part's size in bytes and on average (`PartSize`).
#[derive(Clone, Copy, Debug, Default)]
pub struct PartSize {
    pub bytes: u64,
    pub expected: f64,
}

/// Keep the accounting's digit-collapsing rule visible to tests.
pub fn round_bits(r: &PlanRound, p: &Planned) -> f64 {
    let unit = p.capped();
    bits_of(&p.whole_error(r, &unit))
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn table_distances_is_four_words() {
        // static_assert(sizeof(TableDistances) == 4 * sizeof(u64), plan.h:111).
        assert_eq!(core::mem::size_of::<TableDistances>(), 4 * core::mem::size_of::<u64>());
    }

    #[test]
    fn kind_of_round_holds_the_format_table() {
        let all = [
            (R_SEND_SEED, RoundKind::Seed),
            (R_SEND_ANSWER, RoundKind::Empty),
            (R_BAT, RoundKind::Algebraic),
            (R_BAT_SIGMA, RoundKind::Algebraic),
            (R_SPLIT, RoundKind::Empty),
            (R_PSC_EPSILON, RoundKind::Epsilon),
            (R_PSC_ROUND, RoundKind::Algebraic),
            (R_PSC_Y, RoundKind::Algebraic),
            (R_PSC_VALUES, RoundKind::Empty),
            (R_ZERO, RoundKind::Algebraic),
            (R_LINE, RoundKind::Algebraic),
            (R_LKP_SHIFT, RoundKind::Algebraic),
            (R_JOIN, RoundKind::Algebraic),
            (R_LKP, RoundKind::Algebraic),
            (R_RNG, RoundKind::Bits),
            (R_FOLD_EPSILON, RoundKind::Epsilon),
            (R_FOLD_ROUND, RoundKind::Algebraic),
            (R_LOC, RoundKind::Positions),
            (R_CS, RoundKind::Positions),
            (R_BASE_LAMBDA, RoundKind::Algebraic),
            (R_BASE, RoundKind::Positions),
            (R_SEAL, RoundKind::Seal),
            (R_LAST, RoundKind::Empty),
            (R_REPLY, RoundKind::Empty),
            (R_RECORD, RoundKind::Record),
            (R_LIN_POINT, RoundKind::Algebraic),
            (R_LIN_ZETA, RoundKind::Algebraic),
            (R_LINK_POINT, RoundKind::Algebraic),
            (R_LINK, RoundKind::Positions),
            (R_LINK_PHI, RoundKind::Algebraic),
        ];
        for (name, kind) in all {
            assert_eq!(kind_of_round(name), Some(kind), "{}", name);
        }
        assert_eq!(kind_of_round("not a round"), None);
        assert_eq!(kind_of_round(""), None);
    }

    #[test]
    fn same_setting_compares_every_field() {
        let a = Setting::default();
        assert!(Plan::same_setting(&a, &a.clone()));

        let mut b = a.clone();
        b.field_name = String::from("another");
        assert!(!Plan::same_setting(&a, &b));

        let mut b = a.clone();
        b.p = Big::from_u64(7);
        assert!(!Plan::same_setting(&a, &b));

        for change in 0..6 {
            let mut b = a.clone();
            match change {
                0 => b.degree = 4,
                1 => b.circle = true,
                2 => b.target = 129,
                3 => b.instances = 2,
                4 => b.samples = 2,
                _ => b.saved_coefficient = false,
            }
            assert!(!Plan::same_setting(&a, &b), "change {}", change);
        }

        let mut b = a.clone();
        b.work[ErrorKind::Query as usize][Scope::Shared as usize] = 1;
        assert!(!Plan::same_setting(&a, &b));
    }

    #[test]
    fn the_builder_counts_repeats_and_parts() {
        let mut p = Plan::new(Setting::default());
        assert_eq!(p.parts_, vec![String::from("proof")]);
        assert_eq!(p.scope(), Scope::Request);
        assert_eq!(p.times(), 1);

        p.begin_part("key");
        assert_eq!(p.part_, 1);
        p.begin_part("proof");
        assert_eq!(p.part_, 0);
        p.begin_part("key");
        assert_eq!(p.part_, 1);
        assert_eq!(p.parts_.len(), 2);

        p.push_repeat(2);
        p.push_repeat(3);
        assert_eq!(p.times(), 6);
        let r = p.close_none(R_SEND_ANSWER, "answer");
        assert_eq!(r.count, 6);
        assert_eq!(r.part, 1);
        assert_eq!(r.scope, Scope::Request);
        assert_eq!(r.kind, RoundKind::Empty);
        assert_eq!(r.where_, "answer");
        p.pop_repeat();
        assert_eq!(p.times(), 2);
        p.pop_repeat();
        assert_eq!(p.times(), 1);

        let plan = p.finish();
        assert!(plan.holds());
        assert_eq!(plan.rounds.len(), 1);
        assert_eq!(plan.rounds[0].count, 6);
        assert!(plan.names_of_the_format());
        assert_eq!(plan.parts, vec![String::from("proof"), String::from("key")]);
    }

    #[test]
    fn a_first_part_can_be_chosen() {
        let p = Plan::with_first_part(Setting::default(), "entry");
        assert_eq!(p.parts_, vec![String::from("entry")]);
    }

    #[test]
    fn refuse_keeps_the_first_reason_and_rejects_on_an_empty_one() {
        let mut p = Plan::new(Setting::default());
        assert!(!p.refused());
        p.refuse("first");
        p.refuse("second");
        assert!(p.refused());
        assert_eq!(p.why(), "first");
        assert_eq!(p.finish().cause(), Cause::Refused);

        let mut q = Plan::new(Setting::default());
        q.refuse("");
        assert_eq!(q.why(), "refused, and the caller gave no reason");
    }

    #[test]
    fn repeats_of_zero_and_of_the_full_word_reject_the_plan() {
        let mut p = Plan::new(Setting::default());
        p.push_repeat(0);
        assert_eq!(p.why(), "a repeat of 0 times");
        assert_eq!(p.times(), 1);
        assert!(p.refused());

        let mut q = Plan::new(Setting::default());
        q.push_repeat(u64::MAX);
        assert_eq!(q.times(), u64::MAX);
        q.push_repeat(2);
        assert_eq!(q.why(), "repeats of 2^64 times or more");
        assert_eq!(q.times(), u64::MAX);
        q.pop_repeat();
        q.pop_repeat();
        assert_eq!(q.times(), 1);
    }

    #[test]
    #[should_panic(expected = "Plan: pop_repeat without push_repeat")]
    fn pop_repeat_without_push_panics() {
        Plan::new(Setting::default()).pop_repeat();
    }

    #[test]
    fn finish_refuses_an_open_message_or_repeat() {
        let mut p = Plan::new(Setting::default());
        p.push_repeat(2);
        let f = p.finish();
        assert!(f.refused());
        assert_eq!(f.why_not(), "the plan ends inside a repeat");

        let mut p = Plan::new(Setting::default());
        p.send_scalars("scalars", 1);
        let f = p.finish();
        assert!(f.refused());
        assert_eq!(f.why_not(), "the plan ends in the middle of a prover's message: no round takes it in");
    }

    #[test]
    fn a_root_inside_an_empty_round_rejects_the_plan() {
        let mut p = Plan::new(Setting::default());
        p.send_root("root");
        p.close_none(R_SEND_ANSWER, "answer");
        assert_eq!(
            p.why(),
            alloc::format!(
                "round {}: a root stands in the query of the next verifier's message that is not empty",
                R_SEND_ANSWER
            )
        );
    }

    #[test]
    fn close_fills_the_round_and_adds_the_nonce() {
        let mut s = Setting::default();
        s.set_work(ErrorKind::Field, Scope::Request, 8);
        let mut p = Plan::new(s);
        let work_bits = p.close(
            R_BAT,
            RoundKind::Algebraic,
            ErrorKind::Field,
            &Bound::from_u64(0),
            Priced::AsSaid,
            PlanRound { rows: 5, ..PlanRound::default() },
        );
        assert_eq!(work_bits, 8);
        let plan = p.finish();
        assert!(plan.holds(), "{}", plan.why_not());
        let r = &plan.rounds[0];
        assert_eq!(r.name, R_BAT);
        assert_eq!(r.kind, RoundKind::Algebraic);
        assert_eq!(r.why, ErrorKind::Field);
        assert_eq!(r.scope, Scope::Request);
        assert_eq!((r.count, r.part), (1, 0));
        assert_eq!(r.rows, 5);
        assert_eq!(r.draw_e, 0);
        assert_eq!(r.priced, Priced::AsSaid);
        assert_eq!(r.work_bits, 8);
        assert_eq!(r.message_bytes, 0);
        assert_eq!(plan.messages.len(), 1);
        assert_eq!(plan.messages[0].name, "nonce");
        assert_eq!(plan.messages[0].kind, MessageKind::Nonce);
        assert!(!plan.messages[0].in_chain);
        assert_eq!(plan.messages[0].bytes, 8);
        assert_eq!(plan.messages[0].count, 1);
        let (bytes, expected) = plan.size_of(0);
        assert_eq!(bytes, 8);
        assert!((expected - 8.0).abs() < 1e-12);
    }

    #[test]
    fn close_takes_the_open_prover_message_into_the_round() {
        let mut p = Plan::new(Setting::default());
        p.send_scalars("scalars", 2);
        p.send_answers("answers", 3);
        p.send_root("root");
        let work_bits = p.close(
            R_BAT,
            RoundKind::Algebraic,
            ErrorKind::Field,
            &Bound::from_u64(0),
            Priced::AsSaid,
            PlanRound { rows: 1, ..PlanRound::default() },
        );
        assert_eq!(work_bits, 0);
        let plan = p.finish();
        assert!(plan.holds(), "{}", plan.why_not());
        let r = &plan.rounds[0];
        assert_eq!(r.message_bytes, 2 * 24 + 3 * 24 + 32);
        assert_eq!(r.answers, 3);
        assert_eq!(r.roots, 1);
        assert_eq!(plan.messages.len(), 3);
        assert!(plan.messages.iter().all(|m| m.in_chain));
    }

    #[test]
    fn close_none_takes_the_bytes_and_answers_but_not_the_roots() {
        let mut p = Plan::new(Setting::default());
        p.send_scalars("scalars", 2);
        p.send_answers("answers", 3);
        let r = p.close_none(R_SEND_ANSWER, "answer");
        assert_eq!(r.message_bytes, 2 * 24 + 3 * 24);
        assert_eq!(r.answers, 3);
        assert_eq!(r.roots, 0);
        assert!(p.finish().holds());
    }

    #[test]
    fn close_refuses_more_work_than_the_target_or_the_nonce_has_room_for() {
        let mut s = Setting::default();
        s.set_work(ErrorKind::Field, Scope::Request, 128);
        let mut p = Plan::new(s);
        p.close(
            R_BAT,
            RoundKind::Algebraic,
            ErrorKind::Field,
            &Bound::from_u64(0),
            Priced::AsSaid,
            PlanRound { rows: 1, ..PlanRound::default() },
        );
        assert_eq!(
            p.why(),
            alloc::format!("round {}: more work bits than the target or the nonce has room for", R_BAT)
        );

        let mut s = Setting::default();
        s.set_work(ErrorKind::Field, Scope::Request, 60);
        let mut q = Plan::new(s);
        q.close(
            R_BAT,
            RoundKind::Algebraic,
            ErrorKind::Field,
            &Bound::from_u64(0),
            Priced::AsSaid,
            PlanRound { rows: 1, ..PlanRound::default() },
        );
        assert_eq!(
            q.why(),
            alloc::format!("round {}: more work bits than the target or the nonce has room for", R_BAT)
        );
    }

    #[test]
    #[should_panic(expected = "Plan: close() is for a verifier's message that is not empty")]
    fn close_with_an_empty_verifier_message_panics() {
        let mut p = Plan::new(Setting::default());
        p.close(
            R_SEND_ANSWER,
            RoundKind::Empty,
            ErrorKind::Zero,
            &Bound::from_u64(0),
            Priced::Nothing,
            PlanRound::default(),
        );
    }

    #[test]
    #[should_panic(expected = "Plan: a seal bears no proof of work")]
    fn a_seal_with_work_bits_panics() {
        let mut s = Setting::default();
        s.set_work(ErrorKind::Zero, Scope::Request, 8);
        let mut p = Plan::new(s);
        p.close(
            R_SEAL,
            RoundKind::Seal,
            ErrorKind::Zero,
            &Bound::from_u64(0),
            Priced::Nothing,
            PlanRound::default(),
        );
    }

    #[test]
    #[should_panic(expected = "Plan: a round of the format is planned with another kind than its name's")]
    fn a_round_with_the_wrong_kind_panics() {
        let mut p = Plan::new(Setting::default());
        p.enter(PlanRound { name: String::from(R_BAT), kind: RoundKind::Empty, ..PlanRound::default() });
    }

    #[test]
    fn the_verdict_keeps_the_first_cause() {
        let mut p = Plan::new(Setting::default());
        p.close(
            R_BAT,
            RoundKind::Algebraic,
            ErrorKind::Field,
            &Bound::from_u64(1),
            Priced::Nothing,
            PlanRound { rows: 1, ..PlanRound::default() },
        );
        let f = p.finish();
        assert_eq!(f.cause(), Cause::AboveTheTarget);

        let mut q = Plan::new(Setting::default());
        q.close(
            R_BAT,
            RoundKind::Algebraic,
            ErrorKind::Field,
            &Bound::from_u64(0),
            Priced::Nothing,
            PlanRound { draw_positions: 3, ..PlanRound::default() },
        );
        let f = q.finish();
        assert_eq!(f.cause(), Cause::Word);
    }

    #[test]
    fn file_items_take_the_repeat_and_the_part() {
        let mut p = Plan::new(Setting::default());
        p.file("header", MessageKind::Head, 32, 32.0, 0);
        p.last_message_at("the file");
        assert_eq!(p.messages_.len(), 1);
        assert_eq!(p.messages_[0].name, "header");
        assert_eq!(p.messages_[0].where_, "the file");
        assert_eq!(p.messages_[0].count, 1);
        assert_eq!(p.messages_[0].part, 0);
        assert!(!p.messages_[0].in_chain);

        p.push_repeat(2);
        p.begin_part("key");
        p.file("paths", MessageKind::Paths, 10, 5.0, 7);
        p.file("nothing", MessageKind::Salts, 0, 0.0, 0);
        assert_eq!(p.messages_.len(), 2);
        assert_eq!(p.messages_[1].count, 2);
        assert_eq!(p.messages_[1].part, 1);
        assert_eq!(p.messages_[1].hash_calls, 7);
    }

    #[test]
    fn append_scales_counts_and_sets_the_part() {
        let s = Setting::default();
        let mut b = Plan::new(s.clone());
        b.send_scalars("scalars", 1);
        b.close_none(R_SEND_ANSWER, "answer");
        let bf = b.finish();
        assert!(bf.holds(), "{}", bf.why_not());

        let mut a = Plan::new(s);
        a.push_repeat(2);
        a.begin_part("key");
        a.append(&bf);
        a.pop_repeat();
        let af = a.finish();
        assert!(af.holds(), "{}", af.why_not());
        assert_eq!(af.rounds.len(), 1);
        assert_eq!(af.rounds[0].count, 2);
        assert_eq!(af.rounds[0].part, 1);
        assert_eq!(af.messages.len(), 1);
        assert_eq!(af.messages[0].name, "scalars");
        assert_eq!(af.messages[0].count, 2);
        assert_eq!(af.messages[0].part, 1);
    }

    #[test]
    fn append_refuses_a_refused_plan_or_another_setting() {
        let s = Setting::default();
        let mut b = Plan::new(s.clone());
        b.refuse("no");
        let bf = b.finish();
        let mut a = Plan::new(s.clone());
        a.append(&bf);
        assert!(a.refused());
        assert_eq!(a.why(), "no");

        let mut other = Setting::default();
        other.degree = 4;
        let mut c = Plan::new(other);
        c.close_none(R_SEND_ANSWER, "answer");
        let cf = c.finish();
        let mut d = Plan::new(s);
        d.append(&cf);
        assert!(d.refused());
        assert_eq!(d.why(), "rounds that were priced under another setting are appended");
    }

    #[test]
    fn names_of_the_format_looks_at_every_round() {
        let mut p = Plan::new(Setting::default());
        p.close_none(R_SEND_ANSWER, "answer");
        assert!(p.finish().names_of_the_format());

        let mut q = Plan::new(Setting::default());
        q.enter(PlanRound { name: String::from("invented"), ..PlanRound::default() });
        let f = q.finish();
        assert!(!f.names_of_the_format());
        assert!(f.holds());
    }
}
