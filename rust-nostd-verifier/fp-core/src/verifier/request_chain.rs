//! The verifier's check of a request's segment chain, ported from
//! `verifier/src/vf_request_chain.h`: `ChainCheck` (the calls a sub-proof's checker makes itself)
//! and `chain_verify()` (one `LinkHook` per segment). The frame itself is `ReqFrame` and
//! `req_first()`/`req_later()`/`req_close()`/`req_finish()` (`iop::req`); a segment's equation
//! becomes a claim through `req_row()` (`iop::req_rows`).
#![allow(non_snake_case)] // the C++ names `V`, `ChainCheck`

use alloc::vec::Vec;

use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::iop::context::VerifierContext;
use crate::iop::relation::OracleId;
use crate::iop::req::{
    req_close, req_finish, req_first, req_later, ReqFrame, ReqShape,
};
use crate::iop::req_rows::{req_layout_fault, req_row, ReqEquation, ReqLayout, ReqTerm};

/// One segment's sub-proof, as `chain_verify()` calls it (`LinkHook`, vf_request_chain.h:39-44).
/// `run()` checks what follows commit point `moment`: a prover message of the segment that carries
/// oracle messages (`sent`), counted from 0. After the last one, `claim()` and `terms()` give the
/// segment's equation. Not checked, for a hook or for `ChainCheck::close()`: the equation must be
/// a function of public inputs read by the chain, of what was received and of challenges drawn
/// there.
pub trait LinkHook {
    fn run(
        &mut self,
        moment: u32,
        V: &mut VerifierContext<'_, '_, '_, '_>,
        frame: &ReqFrame,
        sent: &[OracleId],
        calls: &mut HashCalls,
    ) -> bool;
    fn claim(&mut self, target: &mut E, on_masks: &mut Vec<E>);
    fn terms(&mut self) -> Vec<ReqTerm>;
}

/// For each segment the caller calls `first()`, `later()` once for each further commit point,
/// with the sub-proof's parts in between, and `close()`; after the last segment, `finish()`
/// (`ChainCheck`, vf_request_chain.h:63-108). A call out of turn returns false, where the frame
/// would end the process, and so does every call after a false one. Preconditions: the shape and
/// the layout have passed `req_fault()` and `req_layout_fault()`, or the constructor ends the
/// process. The C++ class keeps the hash calls inside the context; the port passes them in.
pub struct ChainCheck<'v, 'x, 'a, 'd, 's> {
    V: &'v mut VerifierContext<'x, 'a, 'd, 's>,
    frame: ReqFrame,
    layout: ReqLayout,
    sent: Vec<OracleId>,
    good: bool,
    in_link: bool,
    /// Of the present link, so far.
    moments: u32,
}

impl<'v, 'x, 'a, 'd, 's> ChainCheck<'v, 'x, 'a, 'd, 's> {
    pub fn new(
        V: &'v mut VerifierContext<'x, 'a, 'd, 's>,
        shape: ReqShape,
        layout: ReqLayout,
    ) -> Self {
        let frame = ReqFrame::new(V.st.codes(), shape, V.ch.plan().set.samples);
        if let Some(fault) = req_layout_fault(V.st.codes(), frame.shape(), &layout) {
            panic!("{}", fault);
        }
        ChainCheck {
            V,
            frame,
            layout,
            sent: Vec::new(),
            good: true,
            in_link: false,
            moments: 0,
        }
    }

    /// Starts the next segment: its plain scalars, commit point 0 and its samples; from the
    /// second segment on, also the opening of the previous segment's group.
    pub fn first(&mut self, calls: &mut HashCalls) -> bool {
        if !self.good || self.in_link || self.frame.link() >= self.links() {
            self.good = false;
            return false;
        }
        self.in_link = true;
        self.moments = 1;
        self.good = req_first(self.V, &mut self.frame, &mut self.sent, calls);
        self.good
    }

    /// The oracle messages of the segment's next commit point and their samples.
    pub fn later(&mut self, calls: &mut HashCalls) -> bool {
        if !self.good
            || !self.in_link
            || self.moments >= self.frame.shape().link[self.frame.link()].moments()
        {
            self.good = false;
            return false;
        }
        self.moments += 1;
        self.good = req_later(self.V, &mut self.frame, &mut self.sent, calls);
        self.good
    }

    /// The sub-proof is over: its equation becomes a linear claim on the segment's group; the
    /// group's linear claims are batched and folded into one.
    pub fn close(&mut self, equation: &ReqEquation, calls: &mut HashCalls) -> bool {
        if !self.good
            || !self.in_link
            || self.moments != self.frame.shape().link[self.frame.link()].moments()
        {
            self.good = false;
            return false;
        }
        self.in_link = false;
        let row = req_row(&self.frame, &self.layout, &mut self.V.st, equation);
        self.V.st.add_row(self.frame.group(), row);
        self.good = req_close(self.V, &mut self.frame, calls);
        self.good
    }

    /// After the last `close()`: the opening of the last segment's group, and the proximity test.
    pub fn finish(&mut self, calls: &mut HashCalls) -> bool {
        if !self.good || self.in_link || self.frame.link() != self.links() {
            self.good = false;
            return false;
        }
        let yes = req_finish(self.V, &mut self.frame, calls);
        self.good = false; // nothing is due any more
        yes
    }

    pub fn frame(&self) -> &ReqFrame {
        &self.frame
    }
    /// At the latest commit point.
    pub fn sent(&self) -> &[OracleId] {
        &self.sent
    }
    /// The verifier's context, for a caller that reads a value between the frame's calls (the
    /// C++ `LinkCtx::V`).
    pub fn ctx(&mut self) -> &mut VerifierContext<'x, 'a, 'd, 's> {
        self.V
    }

    /// `hook.run(moment, V, frame, sent)` with the context, the frame and the ids borrowed from
    /// this check at once (the C++ class passes `V_`, `frame_` and `sent_` directly).
    pub fn run_hook(
        &mut self,
        hook: &mut dyn LinkHook,
        moment: u32,
        calls: &mut HashCalls,
    ) -> bool {
        hook.run(moment, &mut *self.V, &self.frame, &self.sent, calls)
    }

    fn links(&self) -> usize {
        self.frame.shape().link.len()
    }
}

/// The entire check, from the first segment's first message to the end of the proximity test
/// (`chain_verify`, vf_request_chain.h:112-127). `hooks[l]` serves segment l.
pub fn chain_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    shape: ReqShape,
    layout: &ReqLayout,
    hooks: &mut [&mut dyn LinkHook],
    calls: &mut HashCalls,
) -> bool {
    let mut check = ChainCheck::new(V, shape, layout.clone());
    let links = check.frame().shape().link.len();
    assert!(
        hooks.len() == links,
        "the chain: one hook for each link"
    );
    for l in 0..links {
        let moments = check.frame().shape().link[l].moments();
        if !check.first(calls) || !check.run_hook(&mut *hooks[l], 0, calls) {
            return false;
        }
        for moment in 1..moments {
            if !check.later(calls) || !check.run_hook(&mut *hooks[l], moment, calls) {
                return false;
            }
        }
        let mut target = E::default();
        let mut on_masks = Vec::new();
        hooks[l].claim(&mut target, &mut on_masks);
        let equation = ReqEquation {
            terms: hooks[l].terms(),
            on_masks,
            target,
        };
        if !check.close(&equation, calls) {
            return false;
        }
    }
    check.finish(calls)
}

/// The request's shape and the layout of its arrays (`ChainShape`, vf_request_chain.h:51-54):
/// fixed before a proof is read and bound in the hash chain's first query. The port carries the
/// values; binding them is the caller's step.
pub struct ChainShape {
    pub shape: ReqShape,
    pub layout: ReqLayout,
}
