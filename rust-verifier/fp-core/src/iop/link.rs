//! LINK, the verifier's side, ported from `blocks/iop/link.h` (lines 46-482).
//!
//! A LINK proof shows that a further committed table (a leaf of an anchor's table) holds the same
//! entries before the cut as the first table: the two tables' folded rows are sent, sampled and
//! compared by one equality claim on their group, and the opened columns of both tables are
//! checked against their roots by FOLDEQ. The proximity test then reads the group.
//!
//! Ported: `LinkShape` with its getters, `public_fault`, `link_fault`, `link_fold_shape`,
//! `link_message`, the `PublicBytes` impl, `LinkPublic` and `link_bind`,
//! `link_same_table_shape`/`link_same_configuration`/`link_key_fault`, `link_equality_row`,
//! `link_draw`, `LinkLists`/`link_lists`, `LinkRun`, `LinkWhy` and the refusal step names,
//! `Link::verify`, `steps_verify`, `test_verify` and `link_verify`. Not ported, because only a
//! prover's engine, coins and drafts use them: `Link::prove`, `steps_prove`, `test_prove`,
//! `link_prove` and `LinkAccess`.
//!
//! Deviations at the verifier's boundary: `Link::verify` takes the plan as `Rc<Planned>` (the port's
//! shared owned form of C++'s `const Planned&`), lends `HashCalls` explicitly, and clones the two
//! records out of the chain's first query, because the context lends the channel out as a whole.

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;

use super::context::{OracleNotice, VerifierContext};
use super::foldeq::{
    foldeq_columns_verify, foldeq_fault, foldeq_joined, foldeq_weights, priced_table, tensor_below,
    FoldedRow, FoldeqShape, IndexName, IndexReader, IndexRecord, IndexShape, TableRead,
    TableStanding, E_DEGREE,
};
use super::fold::{fold_mask_notice, FoldMask, FoldShape};
use super::iopp::{iopp_fault, iopp_fold_shape, iopp_verify, IoppChoice, IoppStage};
use super::message::{Reader, Writer};
use super::relation::{CodeId, Codes, GroupId, GroupLayout, Part, Row};
use super::send::{send_verify, AnswersRound};
use super::tensor::Tensor;
use crate::chain::public::{Binder, Public, PublicBytes};
use crate::chain::rounds::VerifierRounds;
use crate::chain::session::VerifierSession;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::hash::modes::Digest;
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::{Planned, TableTest};
use crate::numbers::round_names::{R_LINK, R_LINK_PHI, R_LINK_POINT};
use crate::tree::positions::PositionList;

/// Label of LINK's hash chain (`LINK_LABEL`, link.h:49).
pub const LINK_LABEL: u64 = 0x4c4e4b01;

// ---------------------------------------------------------------------------------------------------------------------
// The public shape
// ---------------------------------------------------------------------------------------------------------------------

/// The public parameters of a LINK proof (`LinkShape`, link.h:70-111).
#[derive(Clone, Debug)]
pub struct LinkShape {
    pub table: IndexShape,
    pub columns_first: u64,
    pub columns_further: u64,
    pub code: CodeId,
    pub mask_code: CodeId,
    pub rows: u64,
    pub rows_high: bool,
    pub leaf_class: u32,
    pub masks_ahead: bool,
    pub later: Vec<IoppStage>,
    pub choice: IoppChoice,
}

impl Default for LinkShape {
    /// The C++ member defaults (link.h:70-86).
    fn default() -> Self {
        LinkShape {
            table: IndexShape::default(),
            columns_first: 0,
            columns_further: 0,
            code: 0,
            mask_code: 0,
            rows: 0,
            rows_high: false,
            leaf_class: 0,
            masks_ahead: false,
            later: Vec::new(),
            choice: IoppChoice::default(),
        }
    }
}

impl LinkShape {
    /// `v()` (link.h:88).
    pub fn v(&self) -> u32 {
        self.table.v
    }

    /// `entry_bits()` (link.h:89).
    pub fn entry_bits(&self) -> u32 {
        self.table.cube_bits()
    }

    /// The number of leading message entries compared (`cut`, link.h:90).
    pub fn cut(&self) -> u64 {
        self.table.plain() as u64
    }

    /// The FOLDEQ shape of one side (`side`, link.h:91-99).
    pub fn side(&self, of_the_further_table: bool, samples: u32) -> FoldeqShape {
        let mut f = FoldeqShape::default();
        f.index = self.table.clone();
        f.u.name = String::from(if of_the_further_table {
            "the further table's folded row"
        } else {
            "the first table's folded row"
        });
        f.u.code = self.code;
        f.u.main_rows = self.rows as usize;
        f.u.main_deg = E_DEGREE as u32;
        f.u.answers = samples;
        f.rows_high = self.rows_high;
        f.leaf_class = self.leaf_class;
        f.columns = if of_the_further_table { self.columns_further } else { self.columns_first };
        f
    }

    pub fn first(&self, samples: u32) -> FoldeqShape {
        self.side(false, samples)
    }

    pub fn further(&self, samples: u32) -> FoldeqShape {
        self.side(true, samples)
    }

    /// The stages of the proximity test: the group of the two folded rows, then `later`
    /// (`test`, link.h:102-110).
    pub fn test(&self) -> Vec<IoppStage> {
        let mut st = Vec::new();
        st.push(IoppStage {
            code: self.code,
            mask_code: self.mask_code,
            k: 1 + ceil_log2(self.rows),
            h: 0,
        });
        st.extend(self.later.iter().copied());
        st
    }
}

/// Null, or why `S` is no valid shape, as far as `S` shows it without the codes
/// (`public_fault(const LinkShape&)`, link.h:113-121).
pub fn public_fault(S: &LinkShape) -> Option<&'static str> {
    if let Some(f) = S.table.public_fault() {
        return Some(f);
    }
    if S.columns_first < 1 || S.columns_further < 1 {
        return Some("no column is drawn");
    }
    if S.rows < 1 {
        return Some("a folded row's oracle message has no rows");
    }
    if S.later.is_empty() {
        return Some("the proximity test has one stage");
    }
    for stage in &S.later {
        if let Some(f) = stage.public_fault() {
            return Some(f);
        }
    }
    S.choice.public_fault()
}

/// Null, or what is wrong with `S`, by itself or against the codes that it names
/// (`link_fault`, link.h:123-130). `samples` is the plan's `Setting::samples`.
pub fn link_fault(codes: &Codes, S: &LinkShape, samples: u32) -> Option<&'static str> {
    if let Some(f) = public_fault(S) {
        return Some(f);
    }
    // The further side differs only in its name and in the number of columns.
    if let Some(f) = foldeq_fault(codes, &S.first(samples)) {
        return Some(f);
    }
    if S.mask_code as usize >= codes.mask.len() {
        return Some("the group names a mask code that is not there");
    }
    let mut stage = 0usize;
    iopp_fault(codes, &S.test(), samples, &mut stage) // the stages' codes and sizes fit together
}

/// The test's first fold, as far as its fresh mask needs it (`link_fold_shape`, link.h:132-138).
pub fn link_fold_shape(S: &LinkShape) -> FoldShape {
    let st = S.test();
    let mut F = iopp_fold_shape(&st[0], GroupLayout::default());
    F.mask_leaf_class = S.leaf_class;
    F
}

/// The oracle messages that LINK sends before its proximity test, in order
/// (`link_message`, link.h:139-146).
pub fn link_message(S: &LinkShape, samples: u32) -> Vec<OracleNotice> {
    let mut m = Vec::new();
    m.push(OracleNotice { shape: S.first(samples).u, leaf_class: S.leaf_class });
    m.push(OracleNotice { shape: S.further(samples).u, leaf_class: S.leaf_class });
    if S.masks_ahead {
        m.push(fold_mask_notice(&link_fold_shape(S)));
    }
    m
}

impl PublicBytes for LinkShape {
    /// `public_bytes(Writer&, const LinkShape&)` (link.h:148-152).
    fn public_bytes(&self, w: &mut Writer) {
        self.table.public_bytes(w);
        for x in [self.columns_first, self.columns_further] {
            w.put_u64(x);
        }
        for x in [self.code as u64, self.mask_code as u64, self.rows] {
            w.put_u64(x);
        }
        for x in [
            self.rows_high as u64,
            self.leaf_class as u64,
            self.masks_ahead as u64,
        ] {
            w.put_u64(x);
        }
        w.put_u64(self.later.len() as u64);
        for s in &self.later {
            for x in [s.code as u64, s.mask_code as u64, s.k as u64, s.h as u64] {
                w.put_u64(x);
            }
        }
        self.choice.public_bytes(w);
    }

    fn public_fault(&self) -> Option<&'static str> {
        public_fault(self)
    }
}

/// Handles to what `link_bind` writes into the chain's first query (`LinkPublic`, link.h:159-164).
#[derive(Clone, Debug)]
pub struct LinkPublic {
    pub configuration: Public<Digest>,
    pub codes: Public<Codes>,
    pub shape: Public<LinkShape>,
    pub first: Public<IndexName>,
    pub further: Public<IndexName>,
}

/// `link_bind` (link.h:165-171).
pub fn link_bind(
    b: &mut Binder,
    configuration: &Digest,
    codes: &Codes,
    S: &LinkShape,
    first: &IndexName,
    further: &IndexName,
) -> LinkPublic {
    LinkPublic {
        // The first item after the plan.
        configuration: b.configuration(configuration),
        codes: b.parameter("codes", codes.clone()),
        shape: b.parameter("the link", S.clone()),
        first: b.statement("the first table", first.clone()),
        further: b.statement("the further table", further.clone()),
    }
}

/// The members of a table's shape that the first query holds (`link_same_table_shape`,
/// link.h:176-178). `distances` is not one: `foldeq_columns_verify` compares it where a table's
/// columns are read.
pub fn link_same_table_shape(a: &IndexShape, b: &IndexShape) -> bool {
    a.code == b.code && a.v == b.v && a.answers == b.answers && a.salt_bytes == b.salt_bytes
}

/// `link_same_configuration` (link.h:182).
pub fn link_same_configuration(of_the_table: &Digest, of_the_chain: &Digest) -> bool {
    of_the_table == of_the_chain
}

/// Null, or what is wrong with `key`, by itself or against this table shape (the record's size
/// too) and configuration (`link_key_fault`, link.h:186-191).
pub fn link_key_fault(
    configuration: &Digest,
    table: &IndexShape,
    key: &dyn IndexReader,
) -> Option<&'static str> {
    if let Some(f) = key.fault() {
        return Some(f);
    }
    if !link_same_table_shape(key.shape(), table) {
        return Some("a key has another shape than the link's table");
    }
    if !link_same_configuration(&key.configuration(), configuration) {
        return Some("a key's tree starts from another configuration's digest than the chain names");
    }
    super::foldeq::record_fault(table, key.record())
}

// ---------------------------------------------------------------------------------------------------------------------
// The claims and the draws
// ---------------------------------------------------------------------------------------------------------------------

/// The equality claim `< eq(phi, .) before the cut, first folded message - further folded message >
/// = 0` (`link_equality_row`, link.h:197-214). `cut` is `S.cut()`; an argument only so that a test
/// can use another value.
pub fn link_equality_row(
    S: &LinkShape,
    phi: &[E],
    first: &FoldedRow,
    further: &FoldedRow,
    cut: u64,
) -> Row {
    assert!(
        phi.len() == S.entry_bits() as usize,
        "LINK: the point of comparison has one coordinate for each bit of an entry's number"
    );
    let mut row = Row::plain("LINK: the two folded rows agree before the cut");
    for side in 0..2 {
        let at = if side == 1 { further } else { first };
        let mut pieces = Vec::new();
        tensor_below(
            &Tensor::eq(phi, S.entry_bits(), if side == 1 { -E::one() } else { E::one() }),
            0,
            S.entry_bits(),
            cut,
            &mut pieces,
        );
        for t in pieces {
            row.add(at.oracle, Part::Main, at.lay.on_table(t));
        }
    }
    row
}

/// `count` elements of E from the round (`link_draw`, link.h:216-221).
pub fn link_draw(
    ch: &mut VerifierRounds<'_, '_, '_>,
    round: &str,
    count: u32,
    calls: &mut HashCalls,
) -> Vec<E> {
    let mut from = ch.close_algebraic(round, calls);
    let mut x = Vec::with_capacity(count as usize);
    for _ in 0..count {
        x.push(from.draw(calls));
    }
    x
}

/// The positions of the round `R_LINK`, split in two (`LinkLists`, link.h:229-238).
pub struct LinkLists {
    pub first: PositionList,
    pub further: PositionList,
}

/// `link_lists` (link.h:232-238).
pub fn link_lists(S: &LinkShape, drawn: &PositionList) -> LinkLists {
    assert!(
        drawn.draws().len() as u64 == S.columns_first + S.columns_further
            && drawn.log_n() == S.table.code.log_n,
        "LINK: the plan draws other columns than the shape says"
    );
    LinkLists {
        first: drawn.part(0, S.columns_first as usize),
        further: drawn.part(S.columns_first as usize, S.columns_further as usize),
    }
}

// ---------------------------------------------------------------------------------------------------------------------
// The block
// ---------------------------------------------------------------------------------------------------------------------

/// What the steps before the proximity test leave for it (`LinkRun`, link.h:245-250).
pub struct LinkRun {
    pub gamma: Vec<E>,
    pub phi: Vec<E>,
    pub first: FoldedRow,
    pub further: FoldedRow,
    pub group: GroupId,
    /// Of the test's first fold, if it was sent with the folded rows (`masks_ahead`).
    pub mask: FoldMask,
}

impl Default for LinkRun {
    /// The C++ defaults: no group and no mask yet.
    fn default() -> Self {
        LinkRun {
            gamma: Vec::new(),
            phi: Vec::new(),
            first: FoldedRow::default(),
            further: FoldedRow::default(),
            group: super::relation::NONE_ID,
            mask: FoldMask::default(),
        }
    }
}

/// The values of `LinkWhy::step`: the part of `verify` that rejected (link.h:253).
pub const LINK_REFUSED_KEYS: &str = "the keys";
pub const LINK_REFUSED_STEPS: &str = "before the test";
pub const LINK_REFUSED_TEST: &str = "the proximity test";
pub const LINK_REFUSED_END: &str = "the end";

/// Why a LINK proof was rejected (`LinkWhy`, link.h:258-260). `reason` is text for a log:
/// `link_key_fault`'s, or the channel's for the first failure that it met, or, if the channel has
/// none, the step's name. Both are empty after an accepted proof.
#[derive(Clone, Debug, Default)]
pub struct LinkWhy {
    pub step: &'static str,
    pub reason: String,
}

/// The protocol on one hash chain (`Link`, link.h:309-469).
pub struct Link;

impl Link {
    /// The verifier's side (`Link::verify`, link.h:354-378).
    #[allow(clippy::too_many_arguments)]
    pub fn verify(
        plan: Rc<Planned>,
        configuration: &Digest,
        codes: &Codes,
        S: &LinkShape,
        first_table: TableRead<'_>,
        further: &dyn IndexReader,
        proof: &mut Reader<'_>,
        session: &mut VerifierSession,
        why: Option<&mut LinkWhy>,
        notes: Option<Vec<(String, E)>>,
        calls: &mut HashCalls,
    ) -> bool {
        let first = first_table.reader();
        let mut unused = LinkWhy::default();
        let said: &mut LinkWhy = why.unwrap_or(&mut unused);
        *said = LinkWhy::default();
        if let Some(fault) = link_fault(codes, S, plan.set.samples) {
            panic!("{}", fault);
        }
        if let Some(fault) = link_key_fault(configuration, &S.table, first) {
            *said = LinkWhy { step: LINK_REFUSED_KEYS, reason: String::from(fault) };
            return false;
        }
        if let Some(fault) = link_key_fault(configuration, &S.table, further) {
            *said = LinkWhy { step: LINK_REFUSED_KEYS, reason: String::from(fault) };
            return false;
        }
        let mut binder = Binder::new(LINK_LABEL, plan);
        let x = link_bind(
            &mut binder,
            configuration,
            codes,
            S,
            &IndexName { commitment: first.commitment(), record: first.record().clone() },
            &IndexName { commitment: further.commitment(), record: further.record().clone() },
        );
        let mut ch = VerifierRounds::new(&mut binder, proof, session, calls);
        let mut V = VerifierContext::new(&x.codes, &mut ch);
        V.notes = notes;
        let mut run = LinkRun::default();
        // The C++ lends the records from the chain; the port clones them because the channel is
        // lent out as a whole.
        let shape = V.ch.get(&x.shape).clone();
        let first_record = V.ch.get(&x.first).record.clone();
        let further_record = V.ch.get(&x.further).record.clone();
        if !steps_verify(
            &mut V,
            &shape,
            &first_table,
            &first_record,
            further,
            &further_record,
            shape.cut(),
            &mut run,
            calls,
        ) {
            *said = LinkWhy {
                step: LINK_REFUSED_STEPS,
                reason: String::from(V.ch.why().unwrap_or(LINK_REFUSED_STEPS)),
            };
            return false;
        }
        if !test_verify(&mut V, &shape, &mut run, calls) {
            *said = LinkWhy {
                step: LINK_REFUSED_TEST,
                reason: String::from(V.ch.why().unwrap_or(LINK_REFUSED_TEST)),
            };
            return false;
        }
        if !V.ch.finish() {
            *said = LinkWhy {
                step: LINK_REFUSED_END,
                reason: String::from(V.ch.why().unwrap_or(LINK_REFUSED_END)),
            };
            return false;
        }
        V.st.require_all_tested();
        true
    }
}

/// From gamma to the equality claim (`steps_verify`, link.h:419-462).
#[allow(clippy::too_many_arguments)]
pub fn steps_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &LinkShape,
    first_table: &TableRead<'_>,
    first_record: &IndexRecord,
    further: &dyn IndexReader,
    further_record: &IndexRecord,
    cut: u64,
    out: &mut LinkRun,
    calls: &mut HashCalls,
) -> bool {
    let first = first_table.reader();
    out.gamma = link_draw(V.ch, R_LINK_POINT, S.v(), calls);
    // As the prover's side: gamma's error is for this table.
    V.ch.require_table(&priced_table(&S.table, TableTest::Link));
    let samples = V.ch.plan().set.samples;
    let side_first = S.first(samples);
    let side_further = S.further(samples);
    let eq_gamma = foldeq_weights(&side_first, &out.gamma);
    out.group = V.st.new_group("LINK: the two folded rows", S.code, S.mask_code);

    let (good, ids) = send_verify(V, &link_message(S, samples), AnswersRound::Own, calls);
    if !good {
        return false;
    }
    if S.masks_ahead {
        out.mask.sent_as(ids[2]);
    }
    out.first = foldeq_joined(
        &mut V.st,
        &side_first,
        &first.name(),
        first_record,
        &eq_gamma,
        ids[0],
        out.group,
        calls,
    );
    out.further = foldeq_joined(
        &mut V.st,
        &side_further,
        &further.name(),
        further_record,
        &eq_gamma,
        ids[1],
        out.group,
        calls,
    );
    // `rows` so far: `answers` claims per record, the first table's first.
    let t = V.st.group(out.group).rows[0].target;
    V.note("LINK: the target of the first table's record's first row", t);
    let t = V.st.group(out.group).rows[S.table.answers as usize].target;
    V.note("LINK: the target of the further table's record's first row", t);

    let drawn = {
        let mut from = V.ch.close_positions(R_LINK, calls);
        from.positions(S.table.code.log_n, calls)
    };
    if !V.ch.ok() {
        return false;
    }
    // The plan's split point: see `LinkLists`.
    V.ch.require_first_list(S.columns_first);
    V.ch.require_table(&priced_table(&S.table, TableTest::Link));
    let lists = link_lists(S, &drawn);
    let rows_before = V.st.group(out.group).rows.len();
    if !foldeq_columns_verify(
        V,
        first_table,
        TableTest::Link,
        TableStanding::AlreadyTested,
        &side_first,
        &eq_gamma,
        &lists.first,
        &out.first,
        out.group,
        calls,
    ) {
        return false;
    }
    let further_table = TableRead::untested(further);
    if !foldeq_columns_verify(
        V,
        &further_table,
        TableTest::Link,
        TableStanding::UnderTest,
        &side_further,
        &eq_gamma,
        &lists.further,
        &out.further,
        out.group,
        calls,
    ) {
        return false;
    }
    let t = V.st.group(out.group).rows[rows_before].target;
    V.note("LINK: the fold of the first table's column at its first draw", t);
    let t = V.st.group(out.group).rows[rows_before + S.columns_first as usize].target;
    V.note("LINK: the fold of the further table's column at its first draw", t);

    out.phi = link_draw(V.ch, R_LINK_PHI, S.entry_bits(), calls);
    V.st.add_row(out.group, link_equality_row(S, &out.phi, &out.first, &out.further, cut));
    {
        let mut at_entry_0 = E::one(); // eq(phi, 0)
        for x in &out.phi {
            at_entry_0 = at_entry_0 * (E::one() - *x);
        }
        V.note(
            "LINK: the equality row's coefficient at entry 0 of the first table's folded row",
            at_entry_0,
        );
    }
    V.ch.ok()
}

/// The proximity test's verifier side (`test_verify`, link.h:468).
pub fn test_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    S: &LinkShape,
    x: &mut LinkRun,
    calls: &mut HashCalls,
) -> bool {
    let mask = core::mem::take(&mut x.mask);
    iopp_verify(V, x.group, &S.test(), S.choice, mask, calls)
}

/// `link_verify` (link.h:476-480).
#[allow(clippy::too_many_arguments)]
pub fn link_verify(
    plan: Rc<Planned>,
    configuration: &Digest,
    codes: &Codes,
    S: &LinkShape,
    first: TableRead<'_>,
    further: &dyn IndexReader,
    proof: &mut Reader<'_>,
    session: &mut VerifierSession,
    why: Option<&mut LinkWhy>,
    notes: Option<Vec<(String, E)>>,
    calls: &mut HashCalls,
) -> bool {
    Link::verify(plan, configuration, codes, S, first, further, proof, session, why, notes, calls)
}
