//! The production segment seam: `runLinksH()` (`vf_segments.inc:283-340`) and the frame side of a
//! sub-proof's run (`vf_subproof_segment.h`), ported. `FrameSegment` walks a request's first chain
//! with the same calls as `ChainCheck` (`iop::req`), but takes the channel from the `Tr` that a
//! sub-proof passes to its gate, so that the sub-proof's checked code stays unchanged. The
//! statement and the tree book move in and out of a temporary `VerifierContext` around each frame
//! call: that keeps one mutable borrow of the channel without `unsafe`.
//!
//! What the C++ keeps in `LinkCtx` (the present segment, its arrays and its flags) is here the
//! state of `FrameSegment`; `fixedBeforeTheMatrixF`, `rootInH`, `t2Batch`, `rowWeights` and `doorH`
//! are its `SegmentGate` and `AttentionSegment` methods. Every rejection name is the C++ one.

#![allow(non_snake_case)] // the C++ names `V`, `F`, `T`, `X`, `HRow`

use alloc::format;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::frame::check::RequestPublic;
use crate::frame::configure::Configured;
use crate::frame::files::Subproofs;
use crate::hash::calls::HashCalls;
use crate::iop::context::{TreeBook, VerifierContext};
use crate::iop::laid::IndexWeights;
use crate::iop::member::member_pending_row;
use crate::iop::relation::{Codes, OracleId, Statement};
use crate::iop::req::{
    req_close, req_finish, req_first, req_later, ReqFrame, ReqShape,
};
use crate::iop::req_rows::{req_layout_fault, req_row, ReqEquation, ReqLayout, ReqTerm};
use crate::refusal::{Refusal, Result};
use crate::numbers::codes::ceil_log2;
use crate::verifier::attention_check::{AttentionSegment, AttentionSubProof};
use crate::verifier::engine::{HFork, HRow};
use crate::verifier::head_check::{run_head, HeadCheckInputs};
use crate::verifier::head_plan::HPlanH2;
use crate::verifier::layers_check::{run_layer_g, LayerCheckInputs};
use crate::verifier::layers_plan::{HPlan2, Reads};
use crate::verifier::segment::{t2_fill_l, Tail2};
use crate::verifier::segments::LinkKind;
use crate::verifier::smallness::SegmentGate;
use crate::verifier::stage_context::Hl;
use crate::verifier::stage_layout::{Hdr, Lay};
use crate::verifier::transcript::{tr_batch_open, tr_batch_rows, Tr};
use crate::verifier::weights_layout::WsLay;
use crate::verifier::weights_pending::ws_pending;

/// Runs one frame call with a temporary `VerifierContext` built from the parts and the channel.
fn call_ctx<'a, 'd, 's, R>(
    st: &mut Option<Statement>,
    book: &mut Option<TreeBook>,
    tr: &mut Tr<'_, 'a, 'd, 's>,
    f: impl FnOnce(&mut VerifierContext<'_, 'a, 'd, 's>) -> R,
) -> R {
    let mut v = VerifierContext {
        st: st.take().expect("frame segment: the statement is in use"),
        ch: &mut *tr.one,
        book: book.take().expect("frame segment: the tree book is in use"),
        notes: None,
    };
    let r = f(&mut v);
    *st = Some(v.st);
    *book = Some(v.book);
    r
}

fn named(f: &HFork, suffix: &str) -> Refusal {
    Refusal::named(&format!("{}{}", f.g, suffix))
}

fn internal(f: &HFork, suffix: &str) -> Refusal {
    Refusal::internal(&format!("{}{}", f.g, suffix))
}

/// One segment's frame walk: the state of `LinkCtx` and the chain's frame (`ChainCheck`'s parts).
pub struct FrameSegment {
    pub frame: ReqFrame,
    pub layout: ReqLayout,
    sent: Vec<OracleId>,
    good: bool,
    in_link: bool,
    /// The present segment, counted from 0.
    pub link: usize,
    /// Its commit points so far (the `LinkCtx` counter; `rootInH` advances it).
    pub moments: u32,
    /// The chain's own moment counter (`ChainCheck`'s; `later()` advances it).
    ck_moments: u32,
    /// `array_of[t]`: the segment that committed to tree t, and its name there.
    array_of: Vec<(usize, String)>,
    /// `t2Batch` has drawn the last challenge.
    pub handed: bool,
    /// The segment is closed.
    pub done: bool,
    /// For the log: terms; rows without a product form; written-out weights.
    pub terms: usize,
    pub rows_cut: usize,
    pub written: usize,
    /// The context's owned parts, in use only during a frame call.
    st: Option<Statement>,
    book: Option<TreeBook>,
}

/// Takes the owned parts of `V` out, leaving placeholders of the same shape, so that the channel
/// (which `FrameSegment` does not hold) can be borrowed by the sub-proof's `Tr`.
pub fn take_parts(V: &mut VerifierContext<'_, '_, '_, '_>) -> (Statement, TreeBook) {
    let codes = V.st.codes().clone();
    let salt = V.book.salt_bytes();
    let run = *V.ch.run();
    let configuration = *V.ch.configuration();
    let st = core::mem::replace(&mut V.st, Statement::new(codes));
    let book = core::mem::replace(&mut V.book, TreeBook::new(salt, &run, &configuration));
    (st, book)
}

impl FrameSegment {
    pub fn new(
        codes: &Codes,
        shape: ReqShape,
        layout: ReqLayout,
        samples: u32,
        st: Statement,
        book: TreeBook,
    ) -> Self {
        let frame = ReqFrame::new(codes, shape, samples);
        if let Some(fault) = req_layout_fault(codes, frame.shape(), &layout) {
            panic!("{}", fault);
        }
        FrameSegment {
            frame,
            layout,
            sent: Vec::new(),
            good: true,
            in_link: false,
            link: 0,
            moments: 1,
            ck_moments: 0,
            array_of: Vec::new(),
            handed: false,
            done: false,
            terms: 0,
            rows_cut: 0,
            written: 0,
            st: Some(st),
            book: Some(book),
        }
    }

    /// Starts the next segment (the driver sets these before `first()`).
    pub fn start_link(&mut self, link: usize, array_of: Vec<(usize, String)>) {
        self.link = link;
        self.array_of = array_of;
        self.handed = false;
        self.done = false;
        self.moments = 1;
        self.ck_moments = 0;
    }

    pub fn take_st(&mut self) -> Statement {
        self.st.take().expect("frame segment: the statement is gone")
    }
    pub fn take_book(&mut self) -> TreeBook {
        self.book.take().expect("frame segment: the tree book is gone")
    }
    pub fn st(&self) -> &Statement {
        self.st.as_ref().expect("frame segment: the statement is in use")
    }
    pub fn st_mut(&mut self) -> &mut Statement {
        self.st.as_mut().expect("frame segment: the statement is in use")
    }
    pub fn frame(&self) -> &ReqFrame {
        &self.frame
    }
    pub fn sent(&self) -> &[OracleId] {
        &self.sent
    }
    fn links(&self) -> usize {
        self.frame.shape().link.len()
    }

    /// `ChainCheck::first()`.
    pub fn first(&mut self, tr: &mut Tr<'_, '_, '_, '_>, calls: &mut HashCalls) -> bool {
        if !self.good || self.in_link || self.frame.link() >= self.links() {
            self.good = false;
            return false;
        }
        self.in_link = true;
        self.ck_moments = 1;
        self.moments = 1;
        let Self { st, book, frame, sent, .. } = self;
        let good = call_ctx(st, book, tr, |v| req_first(v, frame, sent, calls));
        self.good = good;
        good
    }

    /// `ChainCheck::later()`.
    pub fn later(&mut self, tr: &mut Tr<'_, '_, '_, '_>, calls: &mut HashCalls) -> bool {
        if !self.good
            || !self.in_link
            || self.ck_moments >= self.frame.shape().link[self.frame.link()].moments()
        {
            self.good = false;
            return false;
        }
        self.ck_moments += 1;
        let Self { st, book, frame, sent, .. } = self;
        let good = call_ctx(st, book, tr, |v| req_later(v, frame, sent, calls));
        self.good = good;
        good
    }

    /// `ChainCheck::close()`: the equation becomes the segment's claim; the group's claims are
    /// batched and folded.
    pub fn close(
        &mut self,
        equation: &ReqEquation,
        tr: &mut Tr<'_, '_, '_, '_>,
        calls: &mut HashCalls,
    ) -> bool {
        if !self.good
            || !self.in_link
            || self.ck_moments != self.frame.shape().link[self.frame.link()].moments()
        {
            self.good = false;
            return false;
        }
        self.in_link = false;
        let Self { st, book, frame, layout, .. } = self;
        let good = call_ctx(st, book, tr, |v| {
            let row = req_row(frame, layout, &mut v.st, equation);
            v.st.add_row(frame.group(), row);
            req_close(v, frame, calls)
        });
        self.good = good;
        good
    }

    /// `ChainCheck::finish()`: the last group's opening and the proximity test.
    pub fn finish(&mut self, tr: &mut Tr<'_, '_, '_, '_>, calls: &mut HashCalls) -> bool {
        if !self.good || self.in_link || self.frame.link() != self.links() {
            self.good = false;
            return false;
        }
        let Self { st, book, frame, .. } = self;
        let yes = call_ctx(st, book, tr, |v| req_finish(v, frame, calls));
        self.good = false;
        yes
    }
}

/// A virtual row's weights in the form that the frame takes (`rowWeights`, vf_subproof_segment.h).
fn row_weights(f: &HFork, x: &crate::verifier::engine::HTree, r: &HRow) -> Result<IndexWeights> {
    let bits = ceil_log2(x.r);
    let np = r.row_point.len();
    let given = !r.row_lo.is_empty() || !r.row_hi.is_empty();
    if np > bits as usize
        || ((r.row_ones || given) && (np != 0 || r.row_first != 0))
        || (r.row_first & ((1u64 << np) - 1)) != 0
        || r.row_first >= x.r
        || (given && (r.row_ones || r.row_lo.len() != bits as usize || r.row_hi.len() != bits as usize))
    {
        return Err(internal(f, "internal-row-form"));
    }
    let mut w = IndexWeights::default();
    for t in 0..bits as usize {
        if given {
            w.lo.push(r.row_lo[t]);
            w.hi.push(r.row_hi[t]);
        } else if r.row_ones {
            w.lo.push(E::one());
            w.hi.push(E::one());
        } else if t < np {
            let z = r.row_point[np - 1 - t];
            w.lo.push(E::one() - z);
            w.hi.push(z);
        } else {
            let one = (r.row_first >> t) & 1 != 0;
            w.lo.push(if one { E::zero() } else { E::one() });
            w.hi.push(if one { E::one() } else { E::zero() });
        }
    }
    let mut all: Vec<E> = alloc::vec![E::one()];
    for t in 0..bits as usize {
        let half = all.len();
        all.resize(2 * half, E::zero());
        let mut i = half;
        while i > 0 {
            i -= 1;
            all[i + half] = all[i] * w.hi[t];
            all[i] = all[i] * w.lo[t];
        }
    }
    for i in 0..x.r as usize {
        if all[i] != r.coef[i] {
            return Err(internal(f, "internal-row-form"));
        }
    }
    Ok(w)
}

impl SegmentGate for FrameSegment {
    /// `fixedBeforeTheMatrixF` (vf_smallness_test_members.inc:424-446).
    fn fixed_before_the_matrix(
        &mut self,
        f: &HFork,
        gt_tree: &[u32],
        u_trees: &[i32; 4],
    ) -> Result<()> {
        let st = match self.st.as_ref() {
            Some(st) => st,
            None => return Err(internal(f, "internal-f-matrix-order")),
        };
        let here = self.link;
        if self.frame.link() != here || here >= self.frame.shape().link.len() {
            return Err(internal(f, "internal-f-matrix-order"));
        }
        let mut fixed = |tree: i32| -> Result<()> {
            if tree < 0 || tree as usize >= self.array_of.len() {
                return Err(internal(f, "internal-f-matrix-order"));
            }
            let at = &self.array_of[tree as usize];
            let a = if at.0 <= here { self.layout.find(at.0, &at.1) } else { None };
            let Some(a) = a else { return Err(internal(f, "internal-f-matrix-order")) };
            if a.message >= self.frame.shape().link[at.0].messages.len() {
                return Err(internal(f, "internal-f-matrix-order"));
            }
            let m = &self.frame.shape().link[at.0].messages[a.message];
            let late = if at.0 == here {
                m.moment >= self.moments
            } else {
                (at.0 as u64 + m.life as u64) < here as u64
            };
            if late {
                return Err(internal(f, "internal-f-matrix-order"));
            }
            if !st.oracle(self.frame.where_(at.0, a.message)).sampled {
                return Err(internal(f, "internal-f-matrix-order"));
            }
            Ok(())
        };
        for &t in gt_tree {
            fixed(t as i32)?;
        }
        for &t in u_trees {
            if t >= 0 {
                fixed(t)?;
            }
        }
        Ok(())
    }

    /// `rootInH` (vf_subproof_segment.h:260-282).
    fn root_in_h(
        &mut self,
        f: &mut HFork,
        tr: &mut Tr<'_, '_, '_, '_>,
        trees: &[i32],
        calls: &mut HashCalls,
    ) -> Result<()> {
        if self.handed || self.done {
            return Err(named(f, "plan-link"));
        }
        let moment = self.moments;
        if !self.later(tr, calls) {
            // `linkRefused()`: the C++ prints `chain: <why>` and refuses `chain-refused`.
            return Err(Refusal::named(&format!("chain-refused-later {:?}", tr.why())));
        }
        self.moments += 1;
        let messages = self.frame.shape().link[self.link].messages.clone();
        let mut named_trees = 0usize;
        for &t in trees {
            if t < 0 || t as usize >= self.array_of.len() || f.trees[t as usize].root {
                return Err(named(f, "plan-link").into());
            }
            let at = &self.array_of[t as usize];
            let a = if at.0 == self.link { self.layout.find(at.0, &at.1) } else { None };
            let Some(a) = a else { return Err(named(f, "plan-link").into()) };
            if messages[a.message].moment != moment {
                return Err(named(f, "plan-link").into());
            }
            f.root_taken(t as usize);
            named_trees += 1;
        }
        let mut laid = 0usize;
        for a in &self.layout.link[self.link] {
            if messages[a.message].moment == moment {
                laid += 1;
            }
        }
        if named_trees != laid {
            return Err(named(f, "plan-link").into());
        }
        Ok(())
    }
}

impl AttentionSegment for FrameSegment {
    /// `t2Batch` (vf_subproof_segment.h:154-166).
    fn batch(
        &mut self,
        f: &mut HFork,
        t: &mut Tail2,
        tr: &mut Tr<'_, '_, '_, '_>,
        used: u32,
        calls: &mut HashCalls,
    ) -> Result<()> {
        if !t.planned || used != f.ns {
            return Err(internal(f, "internal-slot-count"));
        }
        if !t.link
            || self.handed
            || self.moments != self.frame.shape().link[self.link].moments()
        {
            return Err(named(f, "plan-link"));
        }
        t2_fill_l(f, t);
        let theta = tr_batch_open(tr, calls)?;
        f.batch_by(theta)?;
        if f.plan_claims == 0 {
            return Err(internal(f, "internal-f-draws"));
        }
        f.kap_map = alloc::vec![false; f.plan_claims as usize];
        t.used = used;
        self.handed = true;
        Ok(())
    }

    /// `doorH` (vf_subproof_segment.h:326-390).
    fn door_h(
        &mut self,
        f: &mut HFork,
        t: &mut Tail2,
        tr: &mut Tr<'_, '_, '_, '_>,
        equations_laid: u64,
        calls: &mut HashCalls,
    ) -> Result<()> {
        if !t.link || t.walked || self.done {
            return Err(internal(f, "internal-t2-order"));
        }
        t.walked = true;
        // From here on kapTake() ends without a verdict.
        f.door_shut = true;
        if !self.handed {
            return Err(internal(f, "internal-t2-order"));
        }
        if f.plan_claims == 0 || f.n_claim != f.plan_claims {
            return Err(internal(f, "internal-f-door"));
        }
        f.kap_all_taken()?;
        // What is passed on is the weights on the listed arrays, LS and c0; a weight anywhere else
        // would be dropped without a test.
        for ti in t.nt.len()..f.trees.len() {
            for r in &f.trees[ti].rows {
                for x in &r.l {
                    if !x.is_zero() {
                        return Err(internal(f, "internal-f-door"));
                    }
                }
            }
        }
        if self.array_of.len() != t.nt.len() {
            return Err(named(f, "plan-link"));
        }
        let mut eq = ReqEquation { terms: Vec::new(), on_masks: Vec::new(), target: E::zero() };
        for ti in 0..t.nt.len() {
            if t.nt[ti].outside {
                return Err(internal(f, "internal-t2-order"));
            }
            let x = &f.trees[ti];
            for r in &x.rows {
                if r.coef.len() != x.r as usize || r.l.len() != x.k as usize || r.l0 != 0 {
                    return Err(internal(f, &format!("internal-coef-{}", x.name)));
                }
                let l: Rc<Vec<E>> = Rc::new(r.l.clone());
                let mut term = ReqTerm {
                    born: self.array_of[ti].0,
                    array: self.array_of[ti].1.clone(),
                    scale: E::one(),
                    on_rows: IndexWeights::default(),
                    on_columns: IndexWeights::written(l),
                };
                self.written += x.k as usize;
                if r.row_form {
                    term.on_rows = row_weights(f, x, r)?;
                    eq.terms.push(term);
                    continue;
                }
                self.rows_cut += 1;
                // A term takes only one written-out factor; here both are: one term per row with
                // coef not 0.
                for i in 0..x.r {
                    if r.coef[i as usize].is_zero() {
                        continue;
                    }
                    let mut one = term.clone();
                    one.scale = r.coef[i as usize];
                    one.on_rows = IndexWeights::default();
                    let bits = ceil_log2(x.r);
                    for b in 0..bits {
                        let on = (i >> b) & 1 != 0;
                        one.on_rows.lo.push(if on { E::zero() } else { E::one() });
                        one.on_rows.hi.push(if on { E::one() } else { E::zero() });
                    }
                    eq.terms.push(one);
                }
            }
        }
        // The equation on the mask row itself: LS[j] is mask entry j's coefficient, c0 the
        // constant.
        let (ls, c0) = f.settle(t.used)?;
        eq.on_masks = ls;
        eq.target = E::zero() - c0;
        self.terms = eq.terms.len();
        // The channel terminates the program unless the batching round's error was computed for
        // exactly this number of claims and equations.
        tr_batch_rows(tr, f.n_claim as u64 + equations_laid);
        if !self.close(&eq, tr, calls) {
            return Err(Refusal::named(&format!("chain-refused-close {:?}", tr.why())));
        }
        self.done = true;
        Ok(())
    }
}

/// What `runLinksH` needs of the stage (`RunEnv` in the port's names is `SegRun`).
pub struct SegRun<'a> {
    pub links: &'a [crate::verifier::stage_links::LinkMeta],
    pub hid: &'a [HPlan2],
    pub ah: &'a mut [AttentionSubProof],
    pub ph: &'a HPlanH2,
    pub h: &'a Hdr,
    pub y: &'a Lay,
    pub hl: &'a Hl,
    pub reads: &'a Reads,
    pub ws_lay: &'a WsLay,
    pub kl: &'a [u32],
    pub ngr: u64,
    pub p3: bool,
    pub lidb: i32,
    pub limbs: i32,
    pub gcl: i32,
    pub rcl: i32,
    pub tokens: &'a [u32],
    pub y_tok: u32,
    pub win: &'a [u32],
    pub on: &'a [bool],
    pub on_c: &'a [bool],
    pub hrc: u64,
}

/// A failure of `runLinksH`, in the forms that `runLinksH` itself gives it.
pub enum LinkStop {
    /// `ChainCheck::first()` or `finish()` returned false: the callback returns false, and
    /// `check_proof` takes the channel's reason for its `NO` (`check.h:183, 221`).
    False,
    /// Another `refuse()` of the C++: the stage prints `NO: <name>`.
    Refusal(Refusal),
}

impl From<Refusal> for LinkStop {
    fn from(r: Refusal) -> Self {
        LinkStop::Refusal(r)
    }
}

/// `runLinksH()` (`vf_segments.inc:283-340`). `V`'s statement and tree book are moved out for the
/// call and put back before this returns, also on a refusal. `naming_done`: the stage has identified
/// format and commitment (`internal-naming-first`).
#[allow(clippy::too_many_arguments)]
pub fn run_links(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    x: &RequestPublic,
    out: &mut crate::frame::check::LinksResult,
    env: &mut SegRun<'_>,
    naming_done: bool,
    calls: &mut HashCalls,
) -> core::result::Result<(), LinkStop> {
    if !naming_done {
        return Err(Refusal::named("internal-naming-first").into());
    }
    let shape = V.ch.get(&x.shape).clone();
    let layout = V.ch.get(&x.layout).clone();
    let lin_shape = V.ch.get(&x.lin.shape).clone();
    let samples = V.ch.plan().set.samples;
    let codes = V.st.codes().clone();
    let (st, book) = take_parts(V);
    let mut seg = FrameSegment::new(&codes, shape, layout, samples, st, book);
    let r = run_links_core(V, x, out, env, &mut seg, calls, &lin_shape);
    V.st = seg.take_st();
    V.book = seg.take_book();
    r
}

fn run_links_core(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    x: &RequestPublic,
    out: &mut crate::frame::check::LinksResult,
    env: &mut SegRun<'_>,
    seg: &mut FrameSegment,
    calls: &mut HashCalls,
    lin_shape: &crate::iop::lin::LinShape,
) -> core::result::Result<(), LinkStop> {
    let nl = env.links.len();
    for l in 0..nl {
        let meta = &env.links[l];
        seg.start_link(l, meta.array_of.clone());
        let mut tr = Tr::new(&mut *V.ch);
        if !seg.first(&mut tr, calls) {
            // `ChainCheck::first()` returned false: `runLinksH` returns false, and `check_proof`
            // prints the channel's reason as the proof's `NO` (`check.h:183`).
            return Err(LinkStop::False);
        }
        if l == 0 {
            if seg.frame().at_start().len() != 1 {
                return Err(Refusal::named("plan-link").into());
            }
            out.index_masks = seg.frame().at_start()[0];
            let rows: u64 = env.links.iter().map(|y| y.fv as u64).sum();
            let need = rows
                + if rows > 1 {
                    crate::iop::batt::batt_masks(lin_shape.k_col()) as u64
                } else {
                    0
                };
            if (seg.st_mut().masks(out.index_masks).left() as u64) < need {
                return Err(Refusal::named("plan-mask-row").into());
            }
        }
        if seg.frame().plain().len() != if meta.kind == LinkKind::Head { 1 } else { 0 } {
            return Err(Refusal::named("plan-head").into());
        }
        if meta.kind == LinkKind::Head {
            out.reply = seg.frame().plain()[0];
            out.replied = true;
        }
        let mut wo = None;
        match meta.kind {
            LinkKind::Layers => {
                let g = meta.g;
                let inp = LayerCheckInputs {
                    h: env.h,
                    y: env.y,
                    plan: &env.hid[g as usize],
                    reads: env.reads,
                    ws_lay: env.ws_lay,
                    kl: env.kl,
                    g,
                    ngr: env.ngr,
                    p3: env.p3,
                    lidb: env.lidb,
                    limbs: env.limbs,
                    gcl: env.gcl,
                    rcl: env.rcl,
                    tokens: env.tokens,
                };
                let mut f = HFork::default();
                let o = run_layer_g(&inp, &mut f, &mut tr, seg, calls)?;
                wo = Some(o.wo);
            }
            LinkKind::Attention => {
                let g = meta.g as usize;
                let prefix = format!("A{}:", g);
                let s = &mut env.ah[g];
                s.run(&prefix, &mut tr, seg, calls)?;
                wo = None;
            }
            LinkKind::Head => {
                // y, the next token: the chain receives it unmasked at the start of this segment.
                // Its form is tested here; `check_proof` compares it with the client's token.
                {
                    let p = seg.frame().plain();
                    if p[0].0[1].0 != 0 || p[0].0[2].0 != 0 || p[0].0[0].0 >= env.h.v
                    {
                        return Err(Refusal::named("header-y").into());
                    }
                    env.y_tok = p[0].0[0].0 as u32;
                }
                // `if (hOn[T - 1]) win[T - 1] = yTok;` (vf_output_head_check.inc:36): the token
                // checked at the last position is the reply that the proof itself sent, not the
                // caller's. `check_proof` compares the two after the links.
                let mut win = env.win.to_vec();
                let tb = (1usize << env.h.lt).wrapping_sub(1);
                if tb < env.on.len() && env.on[tb] {
                    win[tb] = env.y_tok;
                }
                let inp = HeadCheckInputs {
                    h: env.h,
                    y: env.y,
                    hl: env.hl,
                    plan: env.ph,
                    hid: env.hid,
                    ws_lay: env.ws_lay,
                    ngr: env.ngr,
                    lidb: env.lidb,
                    limbs: env.limbs,
                    y_tok: env.y_tok,
                    win: &win,
                    on: env.on,
                    on_c: env.on_c,
                    hrc: env.hrc,
                };
                let mut f = HFork::default();
                let o = run_head(&inp, &mut f, &mut tr, seg, calls)?;
                wo = Some(o.wo);
            }
        }
        if !seg.handed || !seg.done {
            return Err(Refusal::named("plan-link").into());
        }
        if meta.fv {
            let (o, claims) = match meta.kind {
                LinkKind::Head => (wo.as_ref().unwrap(), env.ph.n_cl as usize),
                LinkKind::Layers => (wo.as_ref().unwrap(), env.hid[meta.g as usize].n_cl),
                LinkKind::Attention => unreachable!("the attention sub-proof has no pending claim"),
            };
            let p = ws_pending(env.ws_lay, o, claims, lin_shape)?;
            let st = seg.st_mut();
            let c = st.masks(out.index_masks).take();
            out.pending.push(member_pending_row(p.g, p.psi, c, p.beta, p.target));
        }
        drop(tr);
    }
    {
        let mut tr = Tr::new(&mut *V.ch);
        if !seg.finish(&mut tr, calls) {
            // `ChainCheck::finish()` returned false: `runLinksH` returns false (`vf_segments.inc:336`).
            return Err(LinkStop::False);
        }
    }
    Ok(())
}
