//! The request's frame, ported from `blocks/iop/req.h` (lines 39-299: the public configuration,
//! the derived groups and sizes, and the checks).
//!
//! A request's proof is a chain of segments (`link` in identifiers), each closed into the next,
//! and one proximity test (`iopp`) at the end. A segment belongs to one sub-proof; its oracle
//! messages are sent at a few commit points (`moment`), and one oracle message may be kept for
//! later segments to read (`life`). Closing a segment batches its claims (BAT), folds them onto a
//! single row (FOLD), and re-encodes that row as the carrying oracle message that the next
//! segment sends in its first prover message.
//!
//! `ReqSizes`, `ReqSubPlan` and `req_plan()` (req.h:306-407) are ported, and the verifier's side
//! of the frame: `ReqFrame` with `req_first()`, `req_later()`, `req_close()` and `req_finish()`
//! (req.h:434-732, `ReqVerifier`). Not ported: `ReqProver`, `ReqSubProver` and `ReqSubVerifier`
//! (the no_std verifier has no prover), and the test-only `req_verify()`.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use super::bat;
use super::context::{tree_sizes, OracleNotice, VerifierContext};
use super::cs::{cs_sigma_verify, Cut, KeptTarget, Switched, SwitchTarget};
use super::foldeq::E_DEGREE;
use super::fold::{fold_mask_notice, fold_verify, FoldMask};
use super::fold_algebra::fold_mask_columns;
use super::iopp::{iopp_fault, iopp_fold_shape, iopp_sized_fault, iopp_verify, IoppChoice, IoppStage};
use super::relation::{
    CodeId, Codes, GroupId, GroupLayout, OracleId, OracleShape, Part, Statement, NONE_ID,
};
use super::send::{send_verify, AnswersRound};
use super::send_pad::sample_cube;
use super::single_rows::SingleRows;
use crate::chain::public::PublicBytes;
use crate::code::code::CODE_MOST_LOG_N;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::iop::message::Writer;
use crate::numbers::blocks::{
    plan_bat, plan_fold, plan_iopp, plan_loc, plan_none, plan_scalars, plan_send, GroupSize,
    SampleSize, Stage, TestedIn, TreeSize,
};
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::Plan;
use crate::numbers::round_names::{R_BAT, R_REPLY};
use crate::numbers::setting::Scope;

/// One oracle message of a segment (`ReqMessage`, req.h:51-56). `life` > 0: later segments read
/// its main rows, and segment l + life (l: its own segment) is the last that does; in segments l
/// to l + life - 1 its rows are kept rows of the group.
#[derive(Clone, Debug, Default)]
pub struct ReqMessage {
    pub shape: OracleShape,
    pub leaf_class: u32,
    /// The prover message of its segment in which it is sent; 0 is the first.
    pub moment: u32,
    /// 0: no later segment reads its main rows.
    pub life: u32,
}

/// One segment (`ReqLink`, req.h:58-72).
#[derive(Clone, Debug, Default)]
pub struct ReqLink {
    pub name: String,
    /// By moment.
    pub messages: Vec<ReqMessage>,
    /// The number of plain scalars, sent unmasked right before the segment's first prover
    /// message; their form and value are for the sub-verifier to check.
    pub plain: u32,
}

impl ReqLink {
    /// `moments()` (req.h:71).
    pub fn moments(&self) -> u32 {
        match self.messages.last() {
            Some(m) => m.moment + 1,
            None => 0,
        }
    }
}

/// The frame's public configuration (`ReqShape`, req.h:75-85).
#[derive(Clone, Debug)]
pub struct ReqShape {
    /// Of every segment's group.
    pub code: CodeId,
    pub mask_code: CodeId,
    pub link: Vec<ReqLink>,
    /// Oracle messages of mask rows only, sent in the very first prover message and belonging to
    /// no group of the frame.
    pub at_start: Vec<OracleNotice>,
    /// The number of answers to the sample of a carrying oracle message.
    pub answers: u32,
    /// The stages of the last test; the first is the group of the last carrying oracle message.
    pub last: Vec<IoppStage>,
    pub choice: IoppChoice,
}

impl Default for ReqShape {
    /// The C++ member defaults (req.h:76-84): `answers` is 1.
    fn default() -> Self {
        ReqShape {
            code: 0,
            mask_code: 0,
            link: Vec::new(),
            at_start: Vec::new(),
            answers: 1,
            last: Vec::new(),
            choice: IoppChoice::default(),
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------------
// Canonical bytes
// ---------------------------------------------------------------------------------------------------------------------

fn put_messages(w: &mut Writer, messages: &[ReqMessage]) {
    w.put_u64(messages.len() as u64);
    for m in messages {
        m.public_bytes(w);
    }
}

fn put_links(w: &mut Writer, links: &[ReqLink]) {
    w.put_u64(links.len() as u64);
    for l in links {
        l.public_bytes(w);
    }
}

fn put_notices(w: &mut Writer, notices: &[OracleNotice]) {
    w.put_u64(notices.len() as u64);
    for n in notices {
        n.public_bytes(w);
    }
}

impl PublicBytes for ReqMessage {
    /// `public_bytes(Writer&, const ReqMessage&)` (req.h:93-95).
    fn public_bytes(&self, w: &mut Writer) {
        for x in [
            self.shape.main_rows as u64,
            if self.shape.main_rows > 0 { self.shape.main_deg as u64 } else { 1 },
            self.shape.mask_rows as u64,
            self.leaf_class as u64,
            self.moment as u64,
            self.life as u64,
        ] {
            w.put_u64(x);
        }
    }
    /// `public_fault(const ReqMessage&)` (req.h:202-214).
    fn public_fault(&self) -> Option<&'static str> {
        public_fault_message(self)
    }
}

impl PublicBytes for ReqLink {
    /// `public_bytes(Writer&, const ReqLink&)` (req.h:96): the name is for prints alone.
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.plain as u64);
        put_messages(w, &self.messages);
    }
    /// `public_fault(const ReqLink&)` (req.h:215-223).
    fn public_fault(&self) -> Option<&'static str> {
        public_fault_link(self)
    }
}

impl PublicBytes for ReqShape {
    /// `public_bytes(Writer&, const ReqShape&)` (req.h:97-100). The last test's first stage is
    /// left out: it is the group of the last carrying oracle message.
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.code as u64);
        w.put_u64(self.mask_code as u64);
        put_links(w, &self.link);
        put_notices(w, &self.at_start);
        w.put_u64(self.answers as u64);
        let later: &[IoppStage] = if self.last.is_empty() { &[] } else { &self.last[1..] };
        w.put_u64(later.len() as u64);
        for s in later {
            s.public_bytes(w);
        }
        self.choice.public_bytes(w);
    }
    /// `public_fault(const ReqShape&)` (req.h:274) is `req_shape_fault()`.
    fn public_fault(&self) -> Option<&'static str> {
        req_shape_fault(self)
    }
}

// ---------------------------------------------------------------------------------------------------------------------
// What follows from the configuration
// ---------------------------------------------------------------------------------------------------------------------

/// One group of oracle messages (`ReqGroup`, req.h:108-112). `k`, `h`: the main rows that are not
/// kept fit in 2^k rows and the mask rows in 2^h, each oracle message's rows rounded up to a power
/// of two; k >= h, k >= 1.
#[derive(Clone, Debug)]
pub struct ReqGroup {
    pub k: u32,
    pub h: u32,
    /// Of the switch into this group; not used for the first.
    pub target: SwitchTarget,
    /// `target.kept[i]`: first sent as (segment, index).
    pub born: Vec<(usize, usize)>,
}

impl Default for ReqGroup {
    fn default() -> Self {
        ReqGroup {
            k: 0,
            h: 0,
            target: SwitchTarget {
                shape: OracleShape::default(),
                leaf_class: 0,
                main: Cut { part: Part::Main, bits: 0, first_row: 0 },
                rest: Cut { part: Part::Main, bits: 0, first_row: 0 },
                kept: Vec::new(),
            },
            born: Vec::new(),
        }
    }
}

/// The segments' groups, then the last test's (`req_groups`, req.h:114-159).
pub fn req_groups(s: &ReqShape) -> Vec<ReqGroup> {
    struct Alive {
        shape: OracleShape,
        leaf_class: u32,
        left: u32,
        born: (usize, usize),
    }
    let block = |rows: usize| -> u64 {
        if rows != 0 {
            1u64 << ceil_log2(rows as u64)
        } else {
            0
        }
    };
    let mut alive: Vec<Alive> = Vec::new();
    let mut groups: Vec<ReqGroup> = Vec::new();
    // The last group (l == link.len()) is the last test's.
    for l in 0..=s.link.len() {
        let mut G = ReqGroup::default();
        let mut main = 0u64;
        let mut mask = 0u64;
        if l > 0 {
            // The carrying oracle message: two main rows over E and no mask rows.
            G.target.shape = OracleShape {
                name: String::from("carried"),
                code: s.code,
                main_rows: 2,
                main_deg: E_DEGREE as u32,
                mask_rows: 0,
                mask_code: 0,
                answers: s.answers,
            };
            G.target.main = Cut { part: Part::Main, bits: 0, first_row: 0 };
            G.target.rest = Cut { part: Part::Main, bits: 0, first_row: 1 };
            main += 2;
        }
        let mut still: Vec<Alive> = Vec::new();
        for a in &alive {
            let k = KeptTarget {
                shape: a.shape.clone(),
                leaf_class: a.leaf_class,
                kept_again: a.left > 1,
            };
            G.target.kept.push(k);
            G.born.push(a.born);
            if a.left > 1 {
                still.push(Alive {
                    shape: a.shape.clone(),
                    leaf_class: a.leaf_class,
                    left: a.left - 1,
                    born: a.born,
                });
            } else {
                main += block(a.shape.main_rows);
            }
        }
        alive = still;
        if l < s.link.len() {
            for (i, m) in s.link[l].messages.iter().enumerate() {
                if m.life > 0 {
                    alive.push(Alive {
                        shape: m.shape.clone(),
                        leaf_class: m.leaf_class,
                        left: m.life,
                        born: (l, i),
                    });
                } else {
                    main += block(m.shape.main_rows);
                }
                mask += block(m.shape.mask_rows);
            }
        }
        G.h = ceil_log2(mask);
        G.k = core::cmp::max(core::cmp::max(ceil_log2(main), G.h), 1);
        groups.push(G);
    }
    groups
}

/// The sizes on which the choice of one distance for all segments' groups depends: the maximum of
/// each number over all groups (`ReqLoad`, req.h:164-169).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReqLoad {
    /// Row variables of a group.
    pub k: u32,
    /// 1 + kept rows, rounded up to a power of two.
    pub slots: u64,
    /// Variables of a sample's cube.
    pub cube_bits: u32,
    /// Claims in a closing <= rows + rows_a_draw * (position draws).
    pub rows: u64,
    pub rows_a_draw: u64,
}

impl Default for ReqLoad {
    /// The C++ member defaults (req.h:165-168): `slots` is 1.
    fn default() -> Self {
        ReqLoad { k: 0, slots: 1, cube_bits: 0, rows: 0, rows_a_draw: 0 }
    }
}

/// `log_ell`, `log_ell_zk`: log2 of the base code's and the mask code's message length.
/// `open_rows[l]`: the number of claims that segment l's sub-proof leaves (`req_load`,
/// req.h:170-195).
pub fn req_load(s: &ReqShape, log_ell: u32, log_ell_zk: u32, open_rows: &[u64]) -> ReqLoad {
    assert!(
        open_rows.len() == s.link.len(),
        "request: one number of open rows for each link"
    );
    let cube = |o: &OracleShape| -> u32 {
        let main = if o.main_rows != 0 { ceil_log2(o.main_rows as u64) + log_ell } else { 0 };
        let mask = if o.mask_rows != 0 { ceil_log2(o.mask_rows as u64) + log_ell_zk } else { 0 };
        if o.main_rows != 0 && o.mask_rows != 0 {
            core::cmp::max(main, mask) + 1
        } else {
            main + mask
        }
    };
    let groups = req_groups(s);
    let mut load = ReqLoad::default();
    for n in &s.at_start {
        load.cube_bits = core::cmp::max(load.cube_bits, cube(&n.shape));
    }
    for l in 0..groups.len() {
        let mut rows = if l < s.link.len() { open_rows[l] } else { 0 };
        let mut kept_before = 0u64;
        let mut kept_here = 0u64;
        if l > 0 {
            rows += 1 + s.answers as u64;
            load.cube_bits = core::cmp::max(load.cube_bits, cube(&groups[l].target.shape));
        }
        for k in &groups[l].target.kept {
            // Its old sample rows and its new ones.
            rows += 2 * k.shape.answers as u64;
            kept_before += k.shape.main_rows as u64;
        }
        if l < s.link.len() {
            for m in &s.link[l].messages {
                rows += m.shape.answers as u64;
                load.cube_bits = core::cmp::max(load.cube_bits, cube(&m.shape));
            }
        }
        if l + 1 < groups.len() {
            for k in &groups[l + 1].target.kept {
                kept_here += k.shape.main_rows as u64;
            }
        }
        load.k = core::cmp::max(load.k, groups[l].k);
        load.slots = core::cmp::max(load.slots, 1u64 << ceil_log2(1 + kept_here));
        load.rows = core::cmp::max(load.rows, rows);
        if l > 0 {
            load.rows_a_draw = core::cmp::max(load.rows_a_draw, 3 + kept_before);
        }
    }
    load
}

// ---------------------------------------------------------------------------------------------------------------------
// The checks
// ---------------------------------------------------------------------------------------------------------------------

/// The largest number of rows of an oracle message (`REQ_MOST_ROWS`, req.h:201).
pub const REQ_MOST_ROWS: usize = 1usize << 20;

/// Null, or what is wrong with one message by itself (`public_fault(const ReqMessage&)`,
/// req.h:202-214).
pub fn public_fault_message(m: &ReqMessage) -> Option<&'static str> {
    if m.shape.main_rows == 0 && m.shape.mask_rows == 0 {
        return Some("an oracle message of the link has no rows");
    }
    if m.shape.main_rows > REQ_MOST_ROWS || m.shape.mask_rows > REQ_MOST_ROWS {
        return Some("an oracle message of the link has more than 2^20 rows");
    }
    if m.shape.main_rows != 0 && m.shape.main_deg != 1 && m.shape.main_deg != E_DEGREE as u32 {
        return Some("main rows of the link are neither over F nor over E");
    }
    let notice = OracleNotice { shape: m.shape.clone(), leaf_class: m.leaf_class };
    if let Some(fault) = notice.public_fault() {
        return Some(fault);
    }
    if m.life > 0 && (m.shape.main_rows == 0 || m.shape.mask_rows > 0) {
        return Some("a kept oracle message has no main rows, or has mask rows");
    }
    // A rule of the design: what a later segment reads is sent, sampled and answered before the
    // sub-proof of the segment that sends it gets its first challenge.
    if m.life > 0 && m.moment != 0 {
        return Some("a kept oracle message does not go in its link's first prover message");
    }
    None
}

/// Null, or what is wrong with one segment by itself (`public_fault(const ReqLink&)`,
/// req.h:215-223).
pub fn public_fault_link(l: &ReqLink) -> Option<&'static str> {
    if l.messages.is_empty() || l.messages[0].moment != 0 {
        return Some("the link has no oracle message at its first moment");
    }
    let mut moment = 0u32;
    for m in &l.messages {
        if m.moment != moment {
            moment += 1;
            if m.moment != moment {
                return Some("the link's oracle messages do not come by moment, or a moment is empty");
            }
        }
        if let Some(fault) = public_fault_message(m) {
            return Some(fault);
        }
    }
    None
}

/// `req_shape_fault()` with the index of the segment that has the fault: `at` is set to the
/// segment counted from 0 (the number of segments if in none) (req.h:224-273).
pub fn req_shape_fault_at(s: &ReqShape, at: &mut usize) -> Option<&'static str> {
    *at = s.link.len();
    if s.link.is_empty() {
        return Some("the request has no link");
    }
    // The soundness argument needs this check and the comparison of every message's number of
    // answers below; without them a parameter file could switch a sample off.
    if s.answers < 1 {
        return Some("no answer to a sample: a carrying oracle message would not be sampled");
    }
    let mut most_class = 0u32;
    for (l, link) in s.link.iter().enumerate() {
        *at = l;
        if let Some(fault) = public_fault_link(link) {
            return Some(fault);
        }
        for m in &link.messages {
            if m.shape.answers != s.answers {
                return Some("an oracle message of the link has another number of answers to its sample than the request");
            }
            if m.shape.main_rows != 0 && m.shape.code != s.code {
                return Some("main rows of the link are under another code than the group's");
            }
            if m.shape.mask_rows != 0 && m.shape.mask_code != s.mask_code {
                return Some("mask rows of the link are under another code than the group's mask code");
            }
            if l + m.life as usize >= s.link.len() {
                return Some("an oracle message is kept beyond the last link");
            }
            most_class = core::cmp::max(most_class, m.leaf_class);
        }
        // A closing folds main rows that are not kept.
        if l == 0
            && !s.link[0]
                .messages
                .iter()
                .any(|m| m.shape.main_rows > 0 && m.life == 0)
        {
            return Some("the first link has no main row that its closing could fold");
        }
    }
    *at = s.link.len();
    for n in &s.at_start {
        // These share no leaf with the segments' oracle messages.
        if n.shape.main_rows != 0 || n.shape.mask_rows == 0 || n.shape.mask_rows > REQ_MOST_ROWS {
            return Some("what rides at the start is not an oracle message of mask rows alone");
        }
        if let Some(fault) = n.public_fault() {
            return Some(fault);
        }
        if n.shape.answers != s.answers {
            return Some("what rides at the start has another number of answers than the request");
        }
        if n.leaf_class <= most_class {
            return Some("what rides at the start is in a leaf class of the links' oracle messages");
        }
    }
    let groups = req_groups(s);
    for l in 0..groups.len() - 1 {
        if groups[l].k > CODE_MOST_LOG_N {
            *at = l;
            return Some("the link's group has too many rows");
        }
    }
    if s.last.len() < 2 {
        return Some("a proximity test has fewer than two stages");
    }
    for stage in &s.last {
        if let Some(fault) = stage.public_fault() {
            return Some(fault);
        }
    }
    if let Some(fault) = s.choice.public_fault() {
        return Some(fault);
    }
    let first = s.last[0];
    let back = groups.last().unwrap();
    if first.code != s.code
        || first.mask_code != s.mask_code
        || first.k != back.k
        || first.h != back.h
    {
        return Some("the last test's first stage is not the group of the last carrying oracle message");
    }
    None
}

/// `req_shape_fault()` (req.h:224-273): checks what the shape shows by itself.
pub fn req_shape_fault(s: &ReqShape) -> Option<&'static str> {
    let mut at = 0usize;
    req_shape_fault_at(s, &mut at)
}

/// `req_fault()` with the index of the segment that has the fault, as `req_shape_fault_at()`
/// (req.h:276-299).
pub fn req_fault_at(codes: &Codes, s: &ReqShape, at: &mut usize) -> Option<&'static str> {
    if let Some(fault) = req_shape_fault_at(s, at) {
        return Some(fault);
    }
    *at = s.link.len();
    if s.code as usize >= codes.base.len() || s.mask_code as usize >= codes.mask.len() {
        return Some("the links' group names a code that is not there");
    }
    let c = &codes.base[s.code as usize];
    let zk = &codes.mask[s.mask_code as usize];
    if s.answers as usize >= c.ell || s.answers as usize >= zk.ell {
        return Some("more answers to a sample than a row has places");
    }
    for n in &s.at_start {
        if n.shape.mask_code as usize >= codes.mask.len() {
            return Some("what rides at the start names a mask code that is not there");
        }
        if n.shape.answers as usize >= codes.mask[n.shape.mask_code as usize].ell {
            return Some("what rides at the start has more answers than a row has places");
        }
    }
    let groups = req_groups(s);
    for l in 0..groups.len() - 1 {
        *at = l;
        if zk.ell < fold_mask_columns(groups[l].k, groups[l].h) {
            return Some("the mask rows are too short for the hiding polynomial of the link's closing");
        }
        let mut carried = 2 * zk.ell as u64 + c.r as u64 + 2 * zk.r as u64 + s.answers as u64;
        for k in &groups[l + 1].target.kept {
            carried += k.shape.main_rows as u64 * c.r as u64
                + k.shape.answers as u64
                    * if k.shape.main_deg == 1 { E_DEGREE as u64 } else { 1 };
        }
        if carried > c.ell as u64 {
            return Some("what the link's closing carries on does not fit one row");
        }
    }
    *at = s.link.len();
    let mut stage = 0usize;
    iopp_fault(codes, &s.last, s.answers, &mut stage)
}

/// Checks the shape against the codes (`req_fault`, req.h:276-299). Null, or the fault; never
/// ends the process, so numbers read from a file can be checked first.
pub fn req_fault(codes: &Codes, s: &ReqShape) -> Option<&'static str> {
    let mut at = 0usize;
    req_fault_at(codes, s, &mut at)
}

// ---------------------------------------------------------------------------------------------------------------------
// The plan
// ---------------------------------------------------------------------------------------------------------------------

/// What the plan needs beyond the configuration (`ReqSizes`, req.h:306-314).
#[derive(Clone, Debug, Default)]
pub struct ReqSizes {
    /// The segments' group: codes, rule, m; `req_plan` sets k, h, slots.
    pub group: GroupSize,
    /// The solved stages of the last test.
    pub last: Vec<Stage>,
    /// For each segment: the number of claims that its sub-proof leaves.
    pub rows: Vec<u64>,
    /// The group in which the `at_start` oracle messages are tested, which is none of the frame's:
    /// a sample's error grows with the list size of its oracle message's group. Not read if there
    /// are none; otherwise it must have a code.
    pub at_start: GroupSize,
}

/// Appends the rounds of a segment's sub-proof that follow the SEND of one of its commit points
/// (`ReqSubPlan`, req.h:316). The C++ header keeps the `OneList` counter in a static; the port
/// passes it in, as the planner functions of `blocks.rs` do.
pub type ReqSubPlan<'a> = dyn Fn(&mut Plan, usize, u32, &mut u64) + 'a;

/// SEND for one prover message of the frame (the local `send` lambda of `req_plan`,
/// req.h:347-352). `riders`: the last `riders` entries of `sent` only ride: they are priced with
/// their own group's list size.
#[allow(clippy::too_many_arguments)]
fn req_send(
    p: &mut Plan,
    codes: &Codes,
    where_: &str,
    sent: &[OracleNotice],
    group: &GroupSize,
    at_start: &GroupSize,
    riders: usize,
    own_round: bool,
    last: &mut u64,
) {
    let mut sampled: Vec<SampleSize> = Vec::new();
    for (i, n) in sent.iter().enumerate() {
        if n.shape.answers > 0 {
            let g = if i + riders < sent.len() { group } else { at_start };
            sampled.push(SampleSize {
                cube_bits: sample_cube(codes, &n.shape).bits,
                groups: TestedIn::new(g),
            });
        }
    }
    let roots = tree_sizes(codes, sent, last).len() as u32;
    plan_send(p, where_, &sampled, roots, own_round);
}

/// Appends every round and message of the frame to the plan `p` (`req_plan`, req.h:322-407), in
/// the order in which ReqProver and ReqVerifier run them. Not checked here: that
/// `req_fault(codes, s)` is null; the caller must have checked it. `last` numbers marked trees
/// (`OneList`), as `OneList::mark` expects; the C++ header keeps that counter in a static.
pub fn req_plan(
    p: &mut Plan,
    codes: &Codes,
    s: &ReqShape,
    z: &ReqSizes,
    sub: &ReqSubPlan<'_>,
    last: &mut u64,
) {
    assert!(
        z.rows.len() == s.link.len() && p.set.samples == s.answers,
        "request: the sizes do not fit the configuration"
    );
    // The round errors are computed from z, the messages' sizes from `codes` and s: both must
    // describe the same codes. Compared here, for the segments' two codes and each stage's in the
    // last test (iopp_sized_fault()).
    assert!(
        z.group.main.log_n == codes.base[s.code as usize].log_n
            && z.group.main.ell == codes.base[s.code as usize].ell as u64
            && z.group.main.r == codes.base[s.code as usize].r as u64
            && z.group.mask.log_n == codes.mask[s.mask_code as usize].log_n
            && z.group.mask.ell == codes.mask[s.mask_code as usize].ell as u64
            && z.group.mask.r == codes.mask[s.mask_code as usize].r as u64,
        "request: the links' group is sized for other codes than the configuration names"
    );
    assert!(!z.last.is_empty(), "request: the last test is sized for no stage");
    let last_fault = iopp_sized_fault(codes, &s.last, &z.last);
    assert!(last_fault.is_none(), "{}", last_fault.unwrap_or(""));
    let groups = req_groups(s);
    assert!(
        s.at_start.is_empty() || z.at_start.main.ell != 0,
        "request: something rides at the start, and the sizes do not say with which list its sample is priced"
    );
    // A sub-proof's planner may change the plan's scope; after each call to it the frame's scope is
    // restored.
    let scope: Scope = p.scope();
    let mut g = z.group.clone(); // of the segment that was closed last
    let mut trees: Vec<TreeSize> = Vec::new(); // that hold the present group's rows
    let mut before = String::new();
    let mut carried_rows = 0u64; // the rows that the last switch leaves on the present group
    for l in 0..groups.len() {
        let is_link = l < s.link.len();
        let where_ = if is_link { s.link[l].name.clone() } else { String::from("last group") };
        let mut sent: Vec<OracleNotice> = Vec::new();
        if l > 0 {
            sent.push(OracleNotice {
                shape: groups[l].target.shape.clone(),
                leaf_class: groups[l].target.leaf_class,
            });
        }
        for k in &groups[l].target.kept {
            sent.push(OracleNotice { shape: k.shape.clone(), leaf_class: k.leaf_class });
        }
        if is_link {
            for m in &s.link[l].messages {
                if m.moment == 0 {
                    sent.push(OracleNotice { shape: m.shape.clone(), leaf_class: m.leaf_class });
                }
            }
        }
        sent.push(fold_mask_notice(&iopp_fold_shape(
            &IoppStage { code: s.code, mask_code: s.mask_code, k: groups[l].k, h: groups[l].h },
            GroupLayout::default(),
        )));
        let first_trees = tree_sizes(codes, &sent, last); // without `at_start`
        let mut sample_rows = 0u64; // of the group's members
        for n in &sent {
            sample_rows += n.shape.answers as u64;
        }
        if l == 0 {
            sent.extend(s.at_start.iter().cloned());
        }
        if is_link && s.link[l].plain > 0 {
            plan_scalars(p, "plain scalars", &where_, s.link[l].plain as u64);
            plan_none(p, R_REPLY, &where_);
        }
        req_send(
            p,
            codes,
            &where_,
            &sent,
            if is_link { &z.group } else { &z.last[0].g },
            &z.at_start,
            if l == 0 { s.at_start.len() } else { 0 },
            l == 0,
            last,
        );
        if l > 0 {
            let t = plan_loc(p, &before, &g, &trees);
            let mut kept_rows = 0u64;
            let mut old_samples = 0u64;
            for k in &groups[l].target.kept {
                kept_rows += k.shape.main_rows as u64;
                old_samples += k.shape.answers as u64;
            }
            carried_rows = 1 + old_samples + t * (3 + kept_rows);
        }
        trees = first_trees;
        if !is_link {
            plan_iopp(
                p,
                &where_,
                &z.last,
                &trees,
                carried_rows + sample_rows,
                0,
                s.choice.masks_ride,
                last,
            );
            break;
        }
        (*sub)(p, l, 0, last);
        p.begin_scope(scope);
        for moment in 1..s.link[l].moments() {
            sent.clear();
            for m in &s.link[l].messages {
                if m.moment == moment {
                    sent.push(OracleNotice { shape: m.shape.clone(), leaf_class: m.leaf_class });
                }
            }
            for n in &sent {
                sample_rows += n.shape.answers as u64;
            }
            req_send(p, codes, &where_, &sent, &z.group, &z.at_start, 0, true, last);
            for t in tree_sizes(codes, &sent, last) {
                trees.push(t);
            }
            (*sub)(p, l, moment, last);
            p.begin_scope(scope);
        }
        let mut kept_rows = 0u64; // of this group: they are folded side by side with each main row
        for k in &groups[l + 1].target.kept {
            kept_rows += k.shape.main_rows as u64;
        }
        g = z.group.clone();
        g.name = where_.clone();
        g.k = groups[l].k;
        g.h = groups[l].h;
        g.slots = 1u64 << ceil_log2(1 + kept_rows);
        let rows = z.rows[l] + carried_rows + sample_rows;
        plan_bat(p, &where_, &TestedIn::new(&g), rows);
        plan_fold(p, &where_, &g, 0);
        before = where_;
    }
}

// ---------------------------------------------------------------------------------------------------------------------
// The frame, as the verifier runs it
// ---------------------------------------------------------------------------------------------------------------------

/// Where the frame is in its sequence (`ReqFrame::Next`, req.h:468).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Next {
    First,
    LaterOrClose,
    Done,
}

/// What both sides keep (`ReqFrame`, req.h:434-498), verifier side. The frame's calls are
/// `req_first()`, `req_later()`, `req_close()` and `req_finish()` below, the verifier's methods
/// (`ReqVerifier`, req.h:657-732) with the context passed in place of the C++ member.
pub struct ReqFrame {
    shape: ReqShape,
    groups: Vec<ReqGroup>,
    next: Next,
    link: usize,
    /// The next commit point of the present segment.
    moment: u32,
    group: GroupId,
    kept_before: Vec<OracleId>,
    at_start: Vec<OracleId>,
    own: Vec<OracleId>,
    plain: Vec<E>,
    /// Of the present segment's closing.
    mask: FoldMask,
    /// What the last closing has left.
    rows: SingleRows,
}

impl ReqFrame {
    /// `ReqFrame(const Codes&, const ReqShape&, unsigned)` (req.h:463-467). `samples`: the
    /// number of answers to a sample in the chain's plan.
    pub fn new(codes: &Codes, shape: ReqShape, samples: u32) -> Self {
        let groups = req_groups(&shape);
        if let Some(fault) = req_fault(codes, &shape) {
            panic!("{}", fault);
        }
        assert!(
            shape.answers == samples,
            "request: the shape has another number of answers to a sample than the plan's setting"
        );
        ReqFrame {
            shape,
            groups,
            next: Next::First,
            link: 0,
            moment: 0,
            group: NONE_ID,
            kept_before: Vec::new(),
            at_start: Vec::new(),
            own: Vec::new(),
            plain: Vec::new(),
            mask: FoldMask::default(),
            rows: SingleRows::default(),
        }
    }

    pub fn shape(&self) -> &ReqShape {
        &self.shape
    }
    /// Of the present segment.
    pub fn group(&self) -> GroupId {
        self.group
    }
    /// The present segment, counted from 0.
    pub fn link(&self) -> usize {
        self.link
    }
    /// The kept oracle messages of earlier segments as sent again in the present one, in the
    /// order of sending.
    pub fn kept_before(&self) -> &[OracleId] {
        &self.kept_before
    }
    pub fn at_start(&self) -> &[OracleId] {
        &self.at_start
    }
    /// The present segment's plain scalars, until the next `req_first()`.
    pub fn plain(&self) -> &[E] {
        &self.plain
    }
    pub fn next(&self) -> Next {
        self.next
    }

    /// The oracle message that was sent as number `message` of segment `born`, as the present
    /// segment has it (`ReqFrame::where`, req.h:448-459). The names are `where` in C++; `where`
    /// is a Rust keyword.
    pub fn where_(&self, born: usize, message: usize) -> OracleId {
        assert!(
            self.next == Next::LaterOrClose,
            "request: no link is under way: its first prover message has not gone, or it is closed"
        );
        if born == self.link {
            assert!(
                message < self.own.len(),
                "request: this oracle message of the link has not been sent yet"
            );
            return self.own[message];
        }
        let list = &self.groups[self.link].born;
        for (i, b) in list.iter().enumerate() {
            if *b == (born, message) {
                return self.kept_before[i];
            }
        }
        panic!("request: the present link does not read this oracle message");
    }

    /// `fold_shape()` (req.h:469-471).
    pub fn fold_shape(&self, l: usize, layout: GroupLayout) -> super::fold::FoldShape {
        iopp_fold_shape(
            &IoppStage {
                code: self.shape.code,
                mask_code: self.shape.mask_code,
                k: self.groups[l].k,
                h: self.groups[l].h,
            },
            layout,
        )
    }

    /// `at_moment()` (req.h:472-477). The C++ returns pointers into the shape; the port clones
    /// the (small) messages so that the frame can borrow itself mutably afterwards.
    fn at_moment(&self, moment: u32) -> Vec<ReqMessage> {
        self.shape.link[self.link]
            .messages
            .iter()
            .filter(|x| x.moment == moment)
            .cloned()
            .collect()
    }

    /// `join()` (req.h:478-481).
    fn join(&mut self, S: &mut Statement, sent: &[ReqMessage], ids: &[OracleId]) {
        for (i, m) in sent.iter().enumerate() {
            S.join(self.group, ids[i], m.life > 0);
            self.own.push(ids[i]);
        }
    }

    /// `begin_link()` (req.h:482-486).
    fn begin_link(&mut self, S: &mut Statement) {
        let name = if self.link < self.shape.link.len() {
            self.shape.link[self.link].name.clone()
        } else {
            String::from("last group")
        };
        self.group = S.new_group(name, self.shape.code, self.shape.mask_code);
        self.moment = 1;
        self.own.clear();
    }
}

/// `ReqVerifier::notices()` (req.h:726-730).
fn notices(own: &[ReqMessage]) -> Vec<OracleNotice> {
    own.iter().map(|m| OracleNotice { shape: m.shape.clone(), leaf_class: m.leaf_class }).collect()
}

/// `ReqVerifier::first()` (req.h:661-687). `ids` receives the ids of the segment's oracle
/// messages of commit point 0.
pub fn req_first(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    frame: &mut ReqFrame,
    ids: &mut Vec<OracleId>,
    calls: &mut HashCalls,
) -> bool {
    assert!(
        frame.next == Next::First && frame.link < frame.shape.link.len(),
        "request: a link's first prover message is not due"
    );
    let own = frame.at_moment(0);
    let mut with = notices(&own);
    with.push(fold_mask_notice(&frame.fold_shape(frame.link, GroupLayout::default())));
    if frame.link == 0 {
        with.extend(frame.shape.at_start.iter().cloned());
    }
    frame.begin_link(&mut V.st);
    frame.plain = vec![E::zero(); frame.shape.link[frame.link].plain as usize];
    for x in frame.plain.iter_mut() {
        if !V.ch.recv_e(x) {
            return false;
        }
    }
    if !frame.plain.is_empty() {
        V.ch.close_empty(R_REPLY, calls);
    }
    ids.clear();
    if frame.link == 0 {
        let (good, got) = send_verify(V, &with, AnswersRound::Own, calls);
        *ids = got;
        if !good {
            return false;
        }
    } else {
        let mut s = Switched::default();
        let target = frame.groups[frame.link].target.clone();
        if !cs_sigma_verify(V, &frame.rows, &target, frame.group, &with, &mut s, calls) {
            return false;
        }
        frame.kept_before = s.kept;
        *ids = s.with;
    }
    frame.mask = FoldMask::default();
    frame.mask.sent_as(ids[own.len()]);
    frame.at_start.extend_from_slice(&ids[own.len() + 1..]);
    ids.truncate(own.len());
    frame.join(&mut V.st, &own, ids);
    frame.next = Next::LaterOrClose;
    true
}

/// `ReqVerifier::later()` (req.h:689-695).
pub fn req_later(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    frame: &mut ReqFrame,
    ids: &mut Vec<OracleId>,
    calls: &mut HashCalls,
) -> bool {
    assert!(
        frame.next == Next::LaterOrClose
            && frame.moment < frame.shape.link[frame.link].moments(),
        "request: the link has no further moment"
    );
    let own = frame.at_moment(frame.moment);
    frame.moment += 1;
    let (good, got) = send_verify(V, &notices(&own), AnswersRound::Own, calls);
    *ids = got;
    if !good {
        return false;
    }
    frame.join(&mut V.st, &own, ids);
    true
}

/// `ReqVerifier::close()` (req.h:697-712).
pub fn req_close(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    frame: &mut ReqFrame,
    calls: &mut HashCalls,
) -> bool {
    assert!(
        frame.next == Next::LaterOrClose
            && frame.moment == frame.shape.link[frame.link].moments(),
        "request: moments of the link are missing"
    );
    let input = V.st.begin_run(frame.group);
    assert!(
        input.layout.k == frame.groups[frame.link].k && input.layout.h == frame.groups[frame.link].h,
        "request: the group is not the planned one"
    );
    let f = frame.fold_shape(frame.link, input.layout.clone());
    let theta = V.ch.close_algebraic(R_BAT, calls).draw(calls);
    V.ch.require_rows(input.rows().len() as u64);
    let row = bat::combine(&V.st, frame.group, input, theta);
    V.note("REQ: the group row's target", row.target);
    let mask = core::mem::take(&mut frame.mask);
    if !fold_verify(V, &f, row, mask, &mut frame.rows, calls) {
        return false;
    }
    V.note("REQ: FOLD's target", frame.rows.target);
    frame.mask = FoldMask::default();
    frame.link += 1;
    frame.next = Next::First;
    V.ch.ok()
}

/// `ReqVerifier::finish()` (req.h:714-723).
pub fn req_finish(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    frame: &mut ReqFrame,
    calls: &mut HashCalls,
) -> bool {
    assert!(
        frame.next == Next::First && frame.link == frame.shape.link.len(),
        "request: links are missing"
    );
    frame.begin_link(&mut V.st);
    let mut s = Switched::default();
    let with = [fold_mask_notice(&frame.fold_shape(frame.link, GroupLayout::default()))];
    let target = frame.groups[frame.link].target.clone();
    if !cs_sigma_verify(V, &frame.rows, &target, frame.group, &with, &mut s, calls) {
        return false;
    }
    frame.mask = FoldMask::default();
    frame.mask.sent_as(s.with[0]);
    frame.next = Next::Done;
    let mask = core::mem::take(&mut frame.mask);
    iopp_verify(V, frame.group, &frame.shape.last, frame.shape.choice, mask, calls)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use crate::code::code::Code;

    fn codes() -> Codes {
        Codes {
            base: vec![Code { log_n: 8, ell: 256, r: 0 }],
            mask: vec![Code { log_n: 3, ell: 8, r: 0 }, Code { log_n: 8, ell: 256, r: 0 }],
        }
    }

    fn shape() -> ReqShape {
        ReqShape {
            code: 0,
            mask_code: 0,
            link: vec![ReqLink {
                name: String::from("link"),
                messages: vec![ReqMessage {
                    shape: OracleShape {
                        name: String::from("message"),
                        code: 0,
                        main_rows: 4,
                        main_deg: 1,
                        mask_rows: 1,
                        mask_code: 0,
                        answers: 1,
                    },
                    leaf_class: 0,
                    moment: 0,
                    life: 0,
                }],
                plain: 0,
            }],
            at_start: Vec::new(),
            answers: 1,
            last: vec![
                IoppStage { code: 0, mask_code: 0, k: 1, h: 0 },
                IoppStage { code: 0, mask_code: 1, k: 0, h: 0 },
            ],
            choice: IoppChoice::default(),
        }
    }

    #[test]
    fn req_fault_accepts_a_minimal_shape() {
        assert_eq!(req_fault(&codes(), &shape()), None);
        let mut at = usize::MAX;
        assert_eq!(req_fault_at(&codes(), &shape(), &mut at), None);
        assert_eq!(at, 1);
    }

    #[test]
    fn req_groups_and_load_follow_the_shape() {
        let s = shape();
        let groups = req_groups(&s);
        assert_eq!(groups.len(), 2);
        assert_eq!((groups[0].k, groups[0].h), (2, 0));
        assert_eq!((groups[1].k, groups[1].h), (1, 0));
        assert_eq!(groups[1].target.shape.main_rows, 2);
        assert_eq!(groups[1].target.shape.main_deg, E_DEGREE as u32);
        assert_eq!(groups[1].target.shape.answers, 1);
        let load = req_load(&s, 8, 3, &[7]);
        assert_eq!(load.k, 2);
        assert_eq!(load.rows, 8);
        assert_eq!(load.rows_a_draw, 3);
        assert_eq!(load.slots, 1);
        assert_eq!(load.cube_bits, 11);
    }

    #[test]
    fn req_shape_fault_requires_an_answer() {
        let mut s = shape();
        s.answers = 0;
        s.link[0].messages[0].shape.answers = 0;
        assert_eq!(
            req_shape_fault(&s),
            Some("no answer to a sample: a carrying oracle message would not be sampled")
        );
    }

    #[test]
    fn req_shape_fault_rejects_a_kept_message_beyond_the_last_link() {
        let mut s = shape();
        let m = &mut s.link[0].messages[0];
        m.shape.mask_rows = 0;
        m.life = 1;
        assert_eq!(
            req_shape_fault(&s),
            Some("an oracle message is kept beyond the last link")
        );
    }

    #[test]
    fn req_shape_fault_rejects_moments_that_skip() {
        let mut s = shape();
        let mut m = s.link[0].messages[0].clone();
        m.moment = 2;
        s.link[0].messages.push(m);
        assert_eq!(
            req_shape_fault(&s),
            Some("the link's oracle messages do not come by moment, or a moment is empty")
        );
    }

    #[test]
    fn req_shape_fault_rejects_a_last_test_of_another_group() {
        let mut s = shape();
        s.last[0].k = 2;
        assert_eq!(
            req_shape_fault(&s),
            Some("the last test's first stage is not the group of the last carrying oracle message")
        );
    }

    #[test]
    fn req_fault_checks_the_codes() {
        let mut s = shape();
        s.code = 1;
        s.link[0].messages[0].shape.code = 1;
        s.last[0].code = 1;
        assert_eq!(
            req_fault(&codes(), &s),
            Some("the links' group names a code that is not there")
        );
    }

    #[test]
    fn public_bytes_of_a_message_leave_out_the_codes() {
        let m = shape().link[0].messages[0].clone();
        let mut a = Writer::default();
        let mut b = Writer::default();
        m.public_bytes(&mut a);
        ReqMessage {
            shape: OracleShape { code: 3, mask_code: 4, ..m.shape.clone() },
            ..m.clone()
        }
        .public_bytes(&mut b);
        assert_eq!(a.data(), b.data());
    }
}
