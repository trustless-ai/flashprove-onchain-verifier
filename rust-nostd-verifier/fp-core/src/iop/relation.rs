//! The running statement of the protocol blocks, ported from `blocks/iop/relation.h`
//! (lines 1-713). Verifier-reachable state only: oracle messages, groups, linear claims, the
//! group layout, BAT's `RunInput`, and the coefficients carried into a group's tables.
//!
//! Deviations, all at the verifier's boundary: the prover's engine terms and hints are absent
//! (S2b-1's verifier never creates them; `Statement::has_no_engine` therefore checks only the
//! tensors' held factors), and `SampleReceipt` is built by the ported send block.

use alloc::collections::BTreeMap;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use super::mask::{MaskLedger, MaskSlot, MaskTerm, SampleReceipt, SendAccess};
use super::tensor::{lies_in_F, Form, Tensor};
use crate::code::code::{mask_fits, Code};
use crate::field::ext::{F, E};
use crate::numbers::codes::ceil_log2;

/// Oracle messages are numbered in the order of sending (`OracleId`, relation.h:43-46).
pub type OracleId = u32;
pub type GroupId = u32;
pub type CodeId = u32;
pub const NONE_ID: u32 = u32::MAX;

/// The main or the mask table of an oracle message (`Part`, relation.h:51).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Part {
    Main,
    Mask,
}

/// All codes of one statement (`Codes`, relation.h:56-59).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Codes {
    pub base: Vec<Code>,
    pub mask: Vec<Code>,
}


/// What is public about an oracle message before it is sent (`OracleShape`, relation.h:65-73).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OracleShape {
    pub name: String,
    pub code: CodeId,
    pub main_rows: usize,
    pub main_deg: u32,
    pub mask_rows: usize,
    pub mask_code: CodeId,
    pub answers: u32,
}

impl Default for OracleShape {
    fn default() -> Self {
        OracleShape {
            name: String::new(),
            code: NONE_ID,
            main_rows: 0,
            main_deg: 1,
            mask_rows: 0,
            mask_code: 0,
            answers: 1,
        }
    }
}

/// A structured coefficient vector on one table (`Term`, relation.h:82-86).
#[derive(Clone, Debug)]
pub struct Term {
    pub oracle: OracleId,
    pub part: Part,
    pub v: Tensor,
}

/// A coefficient on a single entry (`Unit`, relation.h:89-94).
#[derive(Clone, Debug)]
pub struct Unit {
    pub oracle: OracleId,
    pub part: Part,
    pub index: u64,
    pub coeff: E,
}

/// Coefficients written out on `first, first + step, ..` of a table (`Run`, relation.h:103-149).
#[derive(Clone, Debug)]
pub struct Run {
    pub oracle: OracleId,
    pub part: Part,
    pub first: u64,
    pub step: u64,
    own: Vec<E>,
    many: Option<Rc<Vec<F>>>,
    from: usize,
    count: usize,
}

impl Run {
    pub fn own(oracle: OracleId, part: Part, first: u64, step: u64, coeff: Vec<E>) -> Self {
        Run { oracle, part, first, step, own: coeff, many: None, from: 0, count: 0 }
    }
    pub fn shared(
        oracle: OracleId,
        part: Part,
        first: u64,
        step: u64,
        of_many: Rc<Vec<F>>,
        from: usize,
        count: usize,
    ) -> Self {
        assert!(
            from <= of_many.len() && count <= of_many.len() - from,
            "run: the stretch does not lie in its vector"
        );
        Run { oracle, part, first, step, own: Vec::new(), many: Some(of_many), from, count }
    }
    pub fn size(&self) -> usize {
        if self.many.is_some() {
            self.count
        } else {
            self.own.len()
        }
    }
    pub fn at(&self, j: usize) -> E {
        match &self.many {
            Some(v) => E([F(v[self.from + j].0), F::zero(), F::zero()]),
            None => self.own[j],
        }
    }
    /// True if both runs cover the same entries of the same table (`lies_as`).
    pub fn lies_as(&self, o: &Run) -> bool {
        self.oracle == o.oracle
            && self.part == o.part
            && self.first == o.first
            && self.step == o.step
            && self.size() == o.size()
    }
    /// `x * r`, as a run that owns its coefficients (`scaled`).
    pub fn scaled(r: &Run, x: E) -> Run {
        let mut s = Run::own(r.oracle, r.part, r.first, r.step, vec![E::zero(); r.size()]);
        s.add_scaled(r, x);
        s
    }
    /// `this += x * other`, entry by entry (`add_scaled`). Afterwards this run owns its vector.
    pub fn add_scaled(&mut self, other: &Run, x: E) {
        assert!(
            !core::ptr::eq(self, other),
            "run: a run is added to itself, or the two runs lie on different entries"
        );
        assert!(self.lies_as(other), "run: a run is added to itself, or the two runs lie on different entries");
        if let Some(v) = self.many.take() {
            self.own.resize(self.count, E::zero());
            for j in 0..self.count {
                self.own[j] = E([F(v[self.from + j].0), F::zero(), F::zero()]);
            }
            self.from = 0;
            self.count = 0;
        }
        match &other.many {
            Some(v) => {
                let c = &v[other.from..other.from + other.size()];
                for j in 0..self.own.len() {
                    add_product(&mut self.own[j], x, c[j]);
                }
            }
            None => {
                for j in 0..self.own.len() {
                    let c = other.own[j];
                    if lies_in_F(&c) {
                        add_product(&mut self.own[j], x, c.0[0]);
                    } else {
                        self.own[j] = self.own[j] + x * c;
                    }
                }
            }
        }
    }
}

/// `sum += a b`, coordinate by coordinate (`add_product`, tensor.h:45-47).
fn add_product(sum: &mut E, a: E, b: F) {
    for i in 0..3 {
        sum.0[i] = sum.0[i] + a.0[i] * b;
    }
}

/// A whole coefficient vector on the main table of an oracle message (`MainForm`, relation.h:154-157).
#[derive(Clone, Debug)]
pub struct MainForm {
    pub oracle: OracleId,
    pub c: Form,
}

/// A claim's class in BAT's fixed order (`RowKind`, relation.h:162). The C++ default is PLAIN.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowKind {
    Plain,
    Sample,
    Generator,
}

impl Default for RowKind {
    fn default() -> Self {
        RowKind::Plain
    }
}

/// A linear claim (`Row`, relation.h:166-243).
#[derive(Clone, Debug, Default)]
pub struct Row {
    pub name: String,
    pub kind: RowKind,
    pub terms: Vec<Term>,
    pub units: Vec<Unit>,
    pub runs: Vec<Run>,
    pub forms: Vec<MainForm>,
    pub target: E,
}

impl Row {
    pub fn plain(name: impl Into<String>) -> Self {
        Row { name: name.into(), kind: RowKind::Plain, ..Row::default() }
    }
    pub fn add(&mut self, o: OracleId, part: Part, v: Tensor) {
        self.terms.push(Term { oracle: o, part, v });
    }
    pub fn add_form(&mut self, o: OracleId, c: Form) {
        self.forms.push(MainForm { oracle: o, c });
    }
    pub fn add_run(&mut self, o: OracleId, part: Part, first: u64, step: u64, coeff: Vec<E>) {
        self.runs.push(Run::own(o, part, first, step, coeff));
    }
    pub fn add_run_shared(
        &mut self,
        o: OracleId,
        part: Part,
        first: u64,
        step: u64,
        of_many: Rc<Vec<F>>,
        from: usize,
        count: usize,
    ) {
        self.runs.push(Run::shared(o, part, first, step, of_many, from, count));
    }
    pub fn add_unit(&mut self, o: OracleId, part: Part, index: u64, coeff: E) {
        self.units.push(Unit { oracle: o, part, index, coeff });
    }
    /// Uses up a mask entry (`add_mask`, relation.h:188-192).
    pub fn add_mask(&mut self, slot: MaskSlot, coeff: E) {
        let o = slot.oracle();
        let i = slot.index();
        self.add_unit(o, Part::Mask, i as u64, coeff);
    }
    pub fn add_mask_term(&mut self, t: MaskTerm<E>) {
        self.add_mask(t.slot, t.coeff);
    }

    /// The claim's total coefficient on one entry (`coefficient`, relation.h:195-208).
    pub fn coefficient(&self, o: OracleId, part: Part, index: u64) -> E {
        let mut sum = E::zero();
        for t in &self.terms {
            if t.oracle == o && t.part == part {
                sum = sum + t.v.at(index);
            }
        }
        for u in &self.units {
            if u.oracle == o && u.part == part && u.index == index {
                sum = sum + u.coeff;
            }
        }
        for r in &self.runs {
            if r.oracle == o
                && r.part == part
                && index >= r.first
                && (index - r.first) % r.step == 0
                && (index - r.first) / r.step < r.size() as u64
            {
                sum = sum + r.at(((index - r.first) / r.step) as usize);
            }
        }
        for f in &self.forms {
            if f.oracle == o && part == Part::Main {
                sum = sum + f.c.at(index);
            }
        }
        sum
    }

    /// `this += x * (the runs of other, and nothing else of it)` (`add_runs_scaled`).
    pub fn add_runs_scaled(&mut self, other: &Row, x: E) {
        for r in &other.runs {
            if let Some(mine) = self.runs.iter_mut().find(|m| m.lies_as(r)) {
                mine.add_scaled(r, x);
            } else {
                self.runs.push(Run::scaled(r, x));
            }
        }
    }

    /// `this += x * other`, coefficients and target (`add_scaled`).
    pub fn add_scaled(&mut self, other: &Row, x: E) {
        for t in &other.terms {
            let mut v = t.v.clone();
            v.scalar = v.scalar * x;
            self.terms.push(Term { oracle: t.oracle, part: t.part, v });
        }
        for u in &other.units {
            self.units.push(Unit { oracle: u.oracle, part: u.part, index: u.index, coeff: u.coeff * x });
        }
        self.add_runs_scaled(other, x);
        for f in &other.forms {
            let mut c = f.c.clone();
            c.scale(x);
            self.forms.push(MainForm { oracle: f.oracle, c });
        }
        self.target = self.target + x * other.target;
    }
}

/// The coefficients of a group's claim on one kept member (`KeptForm`, relation.h:247-250).
#[derive(Clone, Debug)]
pub struct KeptForm {
    pub oracle: OracleId,
    pub c: Form,
}

impl Default for KeptForm {
    fn default() -> Self {
        KeptForm { oracle: NONE_ID, c: Form::default() }
    }
}

/// One claim on a whole group (`GroupRow`, relation.h:254-260).
#[derive(Clone, Debug, Default)]
pub struct GroupRow {
    pub group: GroupId,
    pub c: Form,
    pub kept: Vec<KeptForm>,
    pub d: Vec<E>,
    pub target: E,
}

/// Where each member's rows lie in a group's tables (`GroupLayout`, relation.h:271-285).
#[derive(Clone, Debug, Default)]
pub struct GroupLayout {
    pub k: u32,
    pub h: u32,
    pub log_ell: u32,
    pub log_ell_zk: u32,
    pub members: Vec<OracleId>,
    pub kept: Vec<bool>,
    pub main_first: Vec<u64>,
    pub mask_first: Vec<u64>,
}

impl GroupLayout {
    pub const NONE: u64 = u64::MAX;
    pub fn find(&self, o: OracleId) -> usize {
        for (i, m) in self.members.iter().enumerate() {
            if *m == o {
                return i;
            }
        }
        panic!("group: this oracle message is not a member");
    }
}

/// What the statement keeps about one oracle message (`Oracle`, relation.h:292-300).
#[derive(Debug)]
pub struct Oracle {
    pub shape: OracleShape,
    pub sampled: bool,
    pub sample_rows: Vec<Row>,
    pub pad: Vec<(Part, u64)>,
    pub groups: Vec<GroupId>,
    pub ledger: Option<MaskLedger>,
    pub spent_as_mask: bool,
}

/// A set of whole oracle messages tested together (`Group`, relation.h:305-313).
#[derive(Clone, Debug)]
pub struct Group {
    pub name: String,
    pub code: CodeId,
    pub mask_code: CodeId,
    pub members: Vec<OracleId>,
    pub kept: Vec<bool>,
    pub rows: Vec<Row>,
    pub in_run: bool,
}

/// What `begin_run` gives BAT (`RunInput`, relation.h:321-333).
#[derive(Clone, Debug, Default)]
pub struct RunInput {
    pub layout: GroupLayout,
    pub(crate) rows: Vec<Row>,
}

impl RunInput {
    pub fn rows(&self) -> &[Row] {
        &self.rows
    }
    pub(crate) fn take_rows(&mut self) -> Vec<Row> {
        core::mem::take(&mut self.rows)
    }
}

/// The running state (`Statement`, relation.h:335-611). Move-only, as in C++.
#[derive(Debug)]
pub struct Statement {
    codes: Codes,
    oracles: Vec<Oracle>,
    groups: Vec<Group>,
    no_engine: bool,
}

impl Statement {
    pub fn new(codes: Codes) -> Self {
        for c in &codes.base {
            assert!(is_power_of_two(c.ell as u64), "statement: a message length is no power of two");
        }
        for c in &codes.mask {
            assert!(is_power_of_two(c.ell as u64), "statement: a message length is no power of two");
        }
        Statement { codes, oracles: Vec::new(), groups: Vec::new(), no_engine: false }
    }

    pub fn has_no_engine(&mut self) {
        self.no_engine = true;
    }
    pub fn codes(&self) -> &Codes {
        &self.codes
    }
    pub fn oracles(&self) -> usize {
        self.oracles.len()
    }
    pub fn groups(&self) -> usize {
        self.groups.len()
    }
    pub fn oracle(&self, o: OracleId) -> &Oracle {
        assert!((o as usize) < self.oracles.len(), "statement: no such oracle message");
        &self.oracles[o as usize]
    }
    pub fn group(&self, g: GroupId) -> &Group {
        assert!((g as usize) < self.groups.len(), "statement: no such group");
        &self.groups[g as usize]
    }

    pub fn row_bits(&self, o: OracleId, part: Part) -> u32 {
        let s = &self.oracle(o).shape;
        ceil_log2(if part == Part::Main { s.main_rows as u64 } else { s.mask_rows as u64 })
    }
    pub fn place_bits(&self, o: OracleId, part: Part) -> u32 {
        let s = &self.oracle(o).shape;
        if !self.has(o, part) {
            return 0;
        }
        match part {
            Part::Main => self.codes.base[s.code as usize].log_ell(),
            Part::Mask => self.codes.mask[s.mask_code as usize].log_ell(),
        }
    }
    pub fn table_bits(&self, o: OracleId, part: Part) -> u32 {
        self.row_bits(o, part) + self.place_bits(o, part)
    }
    pub fn has(&self, o: OracleId, part: Part) -> bool {
        let s = &self.oracle(o).shape;
        (if part == Part::Main { s.main_rows } else { s.mask_rows }) > 0
    }

    pub fn new_group(&mut self, name: impl Into<String>, code: CodeId, mask_code: CodeId) -> GroupId {
        assert!(
            (code as usize) < self.codes.base.len() && (mask_code as usize) < self.codes.mask.len(),
            "statement: no such code"
        );
        assert!(
            mask_fits(&self.codes.base[code as usize], &self.codes.mask[mask_code as usize]),
            "statement: the mask code is longer than the group's"
        );
        self.groups.push(Group {
            name: name.into(),
            code,
            mask_code,
            members: Vec::new(),
            kept: Vec::new(),
            rows: Vec::new(),
            in_run: false,
        });
        (self.groups.len() - 1) as GroupId
    }

    pub fn sent(&mut self, shape: OracleShape) -> OracleId {
        assert!(
            shape.main_rows + shape.mask_rows > 0,
            "statement: an oracle message without rows"
        );
        assert!(
            shape.main_rows == 0 || (shape.code as usize) < self.codes.base.len(),
            "statement: no such base code"
        );
        assert!(
            shape.mask_rows == 0 || (shape.mask_code as usize) < self.codes.mask.len(),
            "statement: no such mask code"
        );
        assert!(
            shape.main_deg == 1 || shape.main_deg == 3,
            "statement: main rows are over F or over E"
        );
        self.oracles.push(Oracle {
            shape,
            sampled: false,
            sample_rows: Vec::new(),
            pad: Vec::new(),
            groups: Vec::new(),
            ledger: None,
            spent_as_mask: false,
        });
        (self.oracles.len() - 1) as OracleId
    }

    pub fn spend_as_mask(&mut self, o: OracleId) {
        let x = self.at_mut(o);
        assert!(
            !x.sampled && x.shape.answers == 0,
            "statement: a masking oracle is never sampled"
        );
        assert!(!x.spent_as_mask, "statement: a masking oracle serves one block only");
        x.spent_as_mask = true;
    }

    /// `sampled` (relation.h:408-419). The pass-key is the ported send block's.
    pub fn sampled(
        &mut self,
        _: &SendAccess,
        o: OracleId,
        sample_rows: Vec<Row>,
        pad: Vec<(Part, u64)>,
        receipt: SampleReceipt,
    ) {
        let x = self.at_mut(o);
        assert!(!x.sampled, "statement: an oracle message is sampled once");
        assert!(
            sample_rows.len() == x.shape.answers as usize && x.shape.answers >= 1,
            "statement: one sample row for each answer"
        );
        assert!(receipt.oracle() == o, "statement: the receipt is another oracle message's");
        x.sampled = true;
        x.sample_rows = sample_rows;
        x.pad = pad;
        for r in &mut x.sample_rows {
            r.kind = RowKind::Sample;
        }
        if x.shape.mask_rows > 0 {
            x.ledger = Some(MaskLedger::new(receipt));
        }
    }

    pub fn sampled_elsewhere(&mut self, mine: OracleId, from: &Statement, theirs: OracleId) {
        assert!(!core::ptr::eq(self, from), "statement: the other statement is this one");
        let y = from.oracle(theirs);
        assert!(y.sampled, "statement: the oracle message has not been sampled in the other statement");
        let mut rows = y.sample_rows.clone();
        let pad = y.pad.clone();
        let (a_main, a_deg, a_mask, a_ans, a_code, a_mask_code) = {
            let s = &self.oracle(mine).shape;
            (s.main_rows, s.main_deg, s.mask_rows, s.answers, s.code, s.mask_code)
        };
        let b = &y.shape;
        assert!(
            a_main == b.main_rows && a_deg == b.main_deg && a_mask == b.mask_rows && a_ans == b.answers,
            "statement: the two oracle messages differ in shape"
        );
        assert!(
            a_main == 0
                || self.codes.base[a_code as usize] == from.codes.base[b.code as usize],
            "statement: the two oracle messages differ in code"
        );
        assert!(
            a_mask == 0
                || self.codes.mask[a_mask_code as usize] == from.codes.mask[b.mask_code as usize],
            "statement: the two oracle messages differ in mask code"
        );
        for r in &mut rows {
            for t in &mut r.terms {
                t.oracle = mine;
            }
            for u in &mut r.units {
                u.oracle = mine;
            }
            for w in &mut r.runs {
                w.oracle = mine;
            }
            for f in &mut r.forms {
                f.oracle = mine;
            }
        }
        let x = self.at_mut(mine);
        assert!(!x.sampled, "statement: an oracle message is sampled once");
        x.sampled = true;
        x.sample_rows = rows;
        x.pad = pad;
    }

    pub fn join(&mut self, g: GroupId, o: OracleId, kept: bool) {
        {
            let G = &self.groups[g as usize];
            let x = &self.oracles[o as usize];
            assert!(x.sampled, "statement: only a sampled oracle message can join a group");
            assert!(!G.in_run, "statement: the proximity test on this group has begun");
            assert!(
                x.shape.main_rows == 0 || x.shape.code == G.code,
                "statement: a group has one base code"
            );
            assert!(
                x.shape.mask_rows == 0 || x.shape.mask_code == G.mask_code,
                "statement: a group has one mask code"
            );
            assert!(!G.members.contains(&o), "statement: already a member");
            assert!(
                !kept || x.shape.main_rows > 0,
                "statement: only main rows can be kept"
            );
        }
        let at_place = self.groups[g as usize].members.partition_point(|m| *m < o);
        self.groups[g as usize].members.insert(at_place, o);
        self.groups[g as usize].kept.insert(at_place, kept);
        self.at_mut(o).groups.push(g);
    }

    pub fn masks(&mut self, o: OracleId) -> &mut MaskLedger {
        let x = self.at_mut(o);
        assert!(
            x.ledger.is_some(),
            "statement: this oracle message has no mask entries to give"
        );
        x.ledger.as_mut().unwrap()
    }

    pub fn add_row(&mut self, g: GroupId, row: Row) {
        {
            let G = &self.groups[g as usize];
            assert!(
                !G.in_run,
                "statement: the rows of a proximity test are fixed before its first challenge"
            );
            assert!(
                row.kind != RowKind::Sample,
                "statement: sample rows come from SEND alone"
            );
            if self.no_engine {
                for t in &row.terms {
                    assert!(
                        !t.v.is_held(),
                        "statement: a verifier's row has a part that only a prover's engine holds"
                    );
                }
                for f in &row.forms {
                    assert!(
                        !f.c.has_held_factor(),
                        "statement: a verifier's row has a part that only a prover's engine holds"
                    );
                }
            }
        }
        let (members, pads) = {
            let G = &self.groups[g as usize];
            let mut pads = Vec::new();
            for o in &G.members {
                for p in &self.oracles[*o as usize].pad {
                    pads.push((*o, *p));
                }
            }
            (G.members.clone(), pads)
        };
        for t in &row.terms {
            self.check_place(&members, t.oracle, t.part, t.v.vars(), 0);
        }
        for u in &row.units {
            self.check_place(&members, u.oracle, u.part, self.table_bits(u.oracle, u.part), u.index);
        }
        for r in &row.runs {
            assert!(
                r.size() != 0 && r.step >= 1,
                "statement: a run of coefficients is empty or has step 0"
            );
            let entries = 1u64 << self.table_bits(r.oracle, r.part);
            assert!(
                r.first < entries && (r.size() as u64 - 1) <= (entries - 1 - r.first) / r.step,
                "statement: no such entry"
            );
            self.check_place(
                &members,
                r.oracle,
                r.part,
                self.table_bits(r.oracle, r.part),
                r.first + r.step * (r.size() as u64 - 1),
            );
        }
        for f in &row.forms {
            self.check_place(&members, f.oracle, Part::Main, self.table_bits(f.oracle, Part::Main), 0);
            assert!(
                f.c.fits(self.table_bits(f.oracle, Part::Main)),
                "statement: a part of a coefficient vector does not fit its table"
            );
        }
        for (o, (part, index)) in pads {
            assert!(
                row.coefficient(o, part, index) == E::zero(),
                "statement: a row reads the pad of a sample"
            );
        }
        self.groups[g as usize].rows.push(row);
    }

    pub fn layout(&self, g: GroupId) -> GroupLayout {
        let G = self.group(g);
        let mut L = GroupLayout {
            k: 0,
            h: 0,
            log_ell: 0,
            log_ell_zk: 0,
            members: G.members.clone(),
            kept: G.kept.clone(),
            main_first: Vec::new(),
            mask_first: Vec::new(),
        };
        L.log_ell = self.codes.base[G.code as usize].log_ell();
        L.log_ell_zk = self.codes.mask[G.mask_code as usize].log_ell();
        let mask_used = self.lay(G, Part::Mask, &mut L.mask_first);
        let main_used = self.lay(G, Part::Main, &mut L.main_first);
        L.h = ceil_log2(mask_used);
        L.k = core::cmp::max(core::cmp::max(ceil_log2(main_used), L.h), 1);
        L
    }

    pub fn begin_run(&mut self, g: GroupId) -> RunInput {
        {
            let G = &mut self.groups[g as usize];
            assert!(!G.in_run, "statement: one proximity test for each group");
            assert!(!G.members.is_empty(), "statement: a group without members");
            G.in_run = true;
        }
        let mut input = RunInput { layout: self.layout(g), rows: Vec::new() };
        let mut rows = core::mem::take(&mut self.groups[g as usize].rows);
        for r in &mut rows {
            if r.kind == RowKind::Plain {
                input.rows.push(core::mem::take(r));
            }
        }
        let members = self.groups[g as usize].members.clone();
        for o in members {
            let x = self.at_mut(o);
            for r in &x.sample_rows {
                input.rows.push(r.clone());
            }
            if let Some(l) = &mut x.ledger {
                l.close();
            }
        }
        for r in &mut rows {
            if r.kind == RowKind::Generator {
                input.rows.push(core::mem::take(r));
            }
        }
        input
    }

    pub fn require_sampled(&self, row: &Row) -> bool {
        let mut ok = true;
        let check = |o: OracleId, ok: &mut bool| {
            if !self.oracle(o).sampled {
                *ok = false;
            }
        };
        for t in &row.terms {
            check(t.oracle, &mut ok);
        }
        for u in &row.units {
            check(u.oracle, &mut ok);
        }
        for r in &row.runs {
            check(r.oracle, &mut ok);
        }
        for f in &row.forms {
            check(f.oracle, &mut ok);
        }
        assert!(ok, "statement: a row names an oracle message that has not been sampled");
        ok
    }

    pub fn require_all_tested(&self) {
        for G in &self.groups {
            assert!(G.in_run, "statement: the protocol ends with a group that has not been tested");
        }
        for x in &self.oracles {
            assert!(
                !x.sampled || !x.groups.is_empty(),
                "statement: the protocol ends with an oracle message that is in no group"
            );
        }
    }

    fn at_mut(&mut self, o: OracleId) -> &mut Oracle {
        assert!((o as usize) < self.oracles.len(), "statement: no such oracle message");
        &mut self.oracles[o as usize]
    }

    fn check_place(&self, members: &[OracleId], o: OracleId, part: Part, vars: u32, index: u64) {
        assert!(
            members.contains(&o),
            "statement: a row on a group names members of that group only"
        );
        assert!(self.has(o, part), "statement: a row names a table that the oracle message does not have");
        assert!(vars == self.table_bits(o, part), "statement: a term does not fit its table");
        assert!(index >> self.table_bits(o, part) == 0, "statement: no such entry");
    }

    fn lay(&self, G: &Group, part: Part, first: &mut Vec<u64>) -> u64 {
        first.clear();
        first.resize(G.members.len(), GroupLayout::NONE);
        let mut order: Vec<usize> = (0..G.members.len())
            .filter(|&i| {
                self.has(G.members[i], part) && !(part == Part::Main && G.kept[i])
            })
            .collect();
        order.sort_by_key(|&i| core::cmp::Reverse(self.row_bits(G.members[i], part)));
        let mut next = 0u64;
        for i in order {
            first[i] = next;
            next += 1u64 << self.row_bits(G.members[i], part);
        }
        next
    }
}

fn is_power_of_two(x: u64) -> bool {
    x != 0 && (x & (x - 1)) == 0
}

/// The index of a member's entry in the group's table (`group_index`, relation.h:619-622).
pub fn group_index(index: u64, row_bits: u32, first: u64, group_row_bits: u32) -> u64 {
    let row = index & ((1u64 << row_bits) - 1);
    let place = index >> row_bits;
    (first + row) + (place << group_row_bits)
}

/// Accumulator for BAT's runs and units (`RowsAside`, relation.h:628-644).
#[derive(Clone, Debug, Default)]
pub struct RowsAside {
    pub sums: Row,
    unit_at: BTreeMap<(OracleId, Part, u64), usize>,
    pub room: Vec<E>,
}

impl RowsAside {
    pub fn add_scaled(&mut self, row: &Row, x: E) {
        self.add_parts_scaled(&row.units, &row.runs, x);
    }
    pub fn add_parts_scaled(&mut self, units: &[Unit], runs: &[Run], x: E) {
        for r in runs {
            if let Some(mine) = self.sums.runs.iter_mut().find(|m| m.lies_as(r)) {
                mine.add_scaled(r, x);
            } else {
                self.sums.runs.push(Run::scaled(r, x));
            }
        }
        for u in units {
            let key = (u.oracle, u.part, u.index);
            if let Some(at) = self.unit_at.get(&key) {
                self.sums.units[*at].coeff = self.sums.units[*at].coeff + times(x, u.coeff);
            } else {
                self.unit_at.insert(key, self.sums.units.len());
                self.sums.units.push(Unit { oracle: u.oracle, part: u.part, index: u.index, coeff: times(x, u.coeff) });
            }
        }
    }
}

/// `a b`, with the multiplication by an element of F shortcut (`times`, tensor.h:44).
pub fn times(a: E, b: E) -> E {
    if lies_in_F(&b) {
        a * b.0[0]
    } else {
        a * b
    }
}

/// `acc += x * row`, with every coefficient carried to the group's tables (`add_to_group_row`,
/// relation.h:651-711).
pub fn add_to_group_row(
    S: &Statement,
    L: &GroupLayout,
    row: Row,
    x: E,
    acc: &mut GroupRow,
    aside: Option<&mut RowsAside>,
) {
    let Row { terms, units, runs, forms, target, .. } = row;
    if acc.d.is_empty() {
        acc.d = vec![E::zero(); 1usize << (L.h + L.log_ell_zk)];
    }
    let mut owned_room: Vec<E> = Vec::new();
    let mut aside = aside;
    {
        let room: &mut Vec<E> = match aside.as_deref_mut() {
            Some(a) => &mut a.room,
            None => &mut owned_room,
        };
        for mut t in terms {
            let i = L.find(t.oracle);
            if t.part == Part::Main && L.kept[i] {
                t.v.scalar = t.v.scalar * x;
                let at = kept_form_at(acc, t.oracle);
                acc.kept[at].c.add(t.v);
                continue;
            }
            let a = S.row_bits(t.oracle, t.part);
            let first = if t.part == Part::Main { L.main_first[i] } else { L.mask_first[i] };
            let bits = if t.part == Part::Main { L.k } else { L.h };
            t.v.scalar = t.v.scalar * x;
            t.v.insert_choice(a, bits - a, first >> a);
            if t.part == Part::Main {
                acc.c.add(t.v);
            } else {
                let mut out = core::mem::take(&mut acc.d);
                t.v.add_to(&mut out, room);
                acc.d = out;
            }
        }
    }
    if let Some(a) = aside.as_deref_mut() {
        a.add_parts_scaled(&units, &runs, x);
    } else {
        for u in &units {
            let i = L.find(u.oracle);
            let a = S.row_bits(u.oracle, u.part);
            carry_entry(S, L, acc, i, u.oracle, u.part, a, u.index, u.coeff, x);
        }
        for r in &runs {
            let i = L.find(r.oracle);
            let a = S.row_bits(r.oracle, r.part);
            for j in 0..r.size() {
                carry_entry(S, L, acc, i, r.oracle, r.part, a, r.first + r.step * j as u64, r.at(j), x);
            }
        }
    }
    for mut f in forms {
        let i = L.find(f.oracle);
        if L.kept[i] {
            let at = kept_form_at(acc, f.oracle);
            acc.kept[at].c.add_ref(&f.c, x);
            continue;
        }
        let a = S.row_bits(f.oracle, Part::Main);
        f.c.insert_choice(a, L.k - a, L.main_first[i] >> a);
        acc.c.add_ref(&f.c, x);
    }
    acc.target = acc.target + x * target;
}

fn kept_form_at(acc: &mut GroupRow, o: OracleId) -> usize {
    let mut at = 0;
    while at < acc.kept.len() && acc.kept[at].oracle < o {
        at += 1;
    }
    if at == acc.kept.len() || acc.kept[at].oracle != o {
        acc.kept.insert(at, KeptForm { oracle: o, c: Form::default() });
    }
    at
}

#[allow(clippy::too_many_arguments)]
fn carry_entry(
    _S: &Statement,
    L: &GroupLayout,
    acc: &mut GroupRow,
    i: usize,
    o: OracleId,
    part: Part,
    a: u32,
    index: u64,
    coeff: E,
    x: E,
) {
    let c = if x == E::one() { coeff } else { times(x, coeff) };
    if part == Part::Mask {
        let at = group_index(index, a, L.mask_first[i], L.h) as usize;
        acc.d[at] = acc.d[at] + c;
    } else if L.kept[i] {
        let at = kept_form_at(acc, o);
        acc.kept[at].c.add_entry(index, c);
    } else {
        acc.c.add_entry(group_index(index, a, L.main_first[i], L.k), c);
    }
}
