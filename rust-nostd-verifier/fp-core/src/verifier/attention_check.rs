//! The attention sub-proof's planning half, ported from `verifier/src/vf_attention_check.h`
//! (through `AttentionSubProof::plan()`).
//!
//! The C++ file also holds `run()`, which reads the proof; the transcript side is added here after
//! the plan. The `AttentionSeam` collects the range check's plan and the chain calls that the
//! sub-proof makes; `run()` will use it with the segment gate.

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::numbers::plan::Plan;
use crate::refusal::{Refusal, Result};
use crate::verifier::common::{WPE, LBZ};

use super::attention_plan::{plan_attention_end, plan_attention_own, AttentionRounds};
use super::attention_shape::{afork_shape_hid, ACall, AFork, S_FD, S_FM, S_RD, S_RM};
use super::engine::{fill_l, HFork};
use super::lookup::{forest_elems, HForest};
use super::matrices::TMat;
use super::segment::{t2_batch, t2_plan, Tail2};
use super::smallness::{HTailF2, OpenGate, SegmentGate, T2Foreign};
use super::sumcheck::{sc3_slots, sumcheck_slots_degrees};
use super::transcript::{tr_batch_open, Tr};
use crate::hash::calls::HashCalls;

/// The range check's seam of the attention sub-proof (`struct AttentionSeam`).
#[derive(Default)]
pub struct AttentionSeam {
    pub tl: HTailF2,
    pub fp: HFork,
    pub tp: Tail2,
    /// The run's copy of the plan's list.
    pub t: Tail2,
    pub n_u: [u64; 3],
}

impl AttentionSeam {
    /// `AttentionSeam::shape`: m: the range check's matrices. `col0F`, `ktO`, `aO` describe the
    /// foreign matrix qa_g.
    pub fn shape(
        &mut self,
        mut m: Vec<TMat>,
        tau: u32,
        col0_f: u64,
        kt_o: u64,
        a_o: u32,
        lidb: i32,
    ) -> Result<()> {
        let mut kq = 0u64;
        for mat in &mut m {
            if mat.kind == 1 {
                mat.foreign = 0;
                mat.tt_off = 0;
                kq = mat.k;
            } else if mat.kind != 0 {
                return Err(Refusal::named("hid-a-weight-matrix"));
            }
        }
        if col0_f != 0 || kt_o != kq {
            return Err(Refusal::named("internal-a-TX-place"));
        }
        let mut f = T2Foreign::default();
        f.name = String::from("PXo");
        f.k = kt_o;
        f.a = a_o;
        for mat in &m {
            if mat.kind == 1 {
                f.m = mat.m;
                f.wp = mat.wp;
            }
        }
        let has_u = [false, false, true, false]; // of U1 to U4, A_g has only U3
        self.tl.shape(&m, &vec![-1i32; m.len()], &[f], has_u, tau, lidb)
    }

    /// `AttentionSeam::iU3`: the index in `HFork::trees` of U3.
    pub fn i_u3(&self) -> u32 {
        self.tl.ix.u[2] as u32
    }

    /// `AttentionSeam::smallElems`.
    pub fn small_elems(&self) -> usize {
        self.tl.small_elems()
    }

    /// `AttentionSeam::plan`.
    pub fn plan(&mut self, n_u3: u64, hb: u32, stated_hb: u32) -> Result<()> {
        self.n_u[2] = n_u3;
        self.fp = HFork::default();
        self.tp = Tail2::default();
        self.tl
            .add_trees(&mut self.fp, &mut self.tp, self.n_u, &[], hb, stated_hb)?;
        if self.fp.trees.len() != 1 + self.tl.pk_mat.len() + 2 + 1 {
            return Err(Refusal::named("internal-a-tree-list"));
        }
        t2_plan(&mut self.fp, &mut self.tp)
    }

    /// `AttentionSeam::start`: starts a run. The chain has already received and sampled the
    /// segment's first oracle messages.
    pub fn start(&mut self, f: &mut HFork, ns: u32) {
        f.trees = self.fp.trees.clone();
        fill_l(f); // the plan keeps no L vector
        self.t = self.tp.clone();
        self.tl.fun_closed = false;
        self.tl.fold_drawn = 0;
        f.slots(ns);
    }

    /// `AttentionSeam::transcript`: reads the range check's messages.
    pub fn transcript<G: SegmentGate + ?Sized>(
        &mut self,
        f: &mut HFork,
        tr: &mut Tr<'_, '_, '_, '_>,
        slot: &mut u32,
        gate: &mut G,
        calls: &mut HashCalls,
    ) -> Result<()> {
        self.tl.transcript(f, tr, slot, &self.t, gate, calls)
    }

    /// `AttentionSeam::batch`: the element that batches the claims, after the last message. The
    /// production seam draws it and records the segment (`t2Batch`); the test seam does the same.
    pub fn batch<G: AttentionSegment + ?Sized>(
        &mut self,
        f: &mut HFork,
        tr: &mut Tr<'_, '_, '_, '_>,
        used: u32,
        gate: &mut G,
        calls: &mut HashCalls,
    ) -> Result<()> {
        gate.batch(f, &mut self.t, tr, used, calls)
    }

    /// `AttentionSeam::objects`: adds the range check's claims.
    pub fn objects(&mut self, f: &mut HFork, fun: &[super::lookup::HFun]) -> Result<()> {
        self.tl.objects(f, fun)
    }

    /// `AttentionSeam::finish`: the self-tests, the coefficients and the equation.
    pub fn finish(
        &mut self,
        f: &mut HFork,
        tr: &mut Tr<'_, '_, '_, '_>,
        gate: &mut dyn AttentionSegment,
        calls: &mut HashCalls,
    ) -> Result<()> {
        let n_u = self.n_u;
        self.tl.self_test(f, n_u)?;
        self.tl.coefficients(f)?;
        self.tl.tile_self_test(f, &self.t)?;
        let equations = self.tl.equations_laid()?;
        gate.door_h(f, &mut self.t, tr, equations, calls)
    }
}

/// The segment calls that the attention sub-proof makes after [`SegmentGate`]'s.
pub trait AttentionSegment: SegmentGate {
    /// `t2Batch`: draws the batching element and fills the virtual rows' weights.
    fn batch(
        &mut self,
        f: &mut HFork,
        t: &mut Tail2,
        tr: &mut Tr<'_, '_, '_, '_>,
        used: u32,
        calls: &mut HashCalls,
    ) -> Result<()>;
    /// `doorH`: passes the one equation on and closes the segment.
    fn door_h(
        &mut self,
        f: &mut HFork,
        t: &mut Tail2,
        tr: &mut Tr<'_, '_, '_, '_>,
        equations_laid: u64,
        calls: &mut HashCalls,
    ) -> Result<()>;
}

/// The test seam: [`OpenGate`]'s checks plus a batching draw and the equation's own checks. It is
/// not the frame check that the sub-proof layer installs.
#[derive(Default)]
pub struct OpenSegment {
    pub gate: OpenGate,
}

impl SegmentGate for OpenSegment {
    fn fixed_before_the_matrix(
        &mut self,
        f: &HFork,
        gt_tree: &[u32],
        u_trees: &[i32; 4],
    ) -> Result<()> {
        self.gate.fixed_before_the_matrix(f, gt_tree, u_trees)
    }

    fn root_in_h(
        &mut self,
        f: &mut HFork,
        tr: &mut Tr<'_, '_, '_, '_>,
        trees: &[i32],
        calls: &mut HashCalls,
    ) -> Result<()> {
        self.gate.root_in_h(f, tr, trees, calls)
    }
}

impl AttentionSegment for OpenSegment {
    fn batch(
        &mut self,
        f: &mut HFork,
        t: &mut Tail2,
        tr: &mut Tr<'_, '_, '_, '_>,
        used: u32,
        calls: &mut HashCalls,
    ) -> Result<()> {
        let theta = tr_batch_open(tr, calls)?;
        t2_batch(f, t, theta, used)
    }

    fn door_h(
        &mut self,
        f: &mut HFork,
        t: &mut Tail2,
        tr: &mut Tr<'_, '_, '_, '_>,
        equations_laid: u64,
        _calls: &mut HashCalls,
    ) -> Result<()> {
        if t.walked {
            return Err(Refusal::internal(&format!("{}internal-t2-order", f.g)));
        }
        if f.plan_claims == 0 || f.n_claim != f.plan_claims {
            return Err(Refusal::internal(&format!("{}internal-f-door", f.g)));
        }
        f.kap_all_taken()?;
        let _ = f.settle(t.used)?;
        // The channel expects the number of rows that the batching round batched.
        super::transcript::tr_batch_rows(tr, f.n_claim as u64 + equations_laid);
        t.walked = true;
        Ok(())
    }
}

/// `AttentionSubProofInputs`.
#[derive(Clone, Debug, Default)]
pub struct AttentionSubProofInputs {
    pub hb: u32,
    pub gid: u32,
    pub kt_o: u64,
    pub col0_q: u64,
    pub a_o: u32,
    pub mid_q: u64,
    /// TMat::wp by matrix.
    pub wp_s: u32,
    pub wp_h: u32,
    pub wp_o: u32,
    pub wp_b_a: u32,
    pub wp_q: u32,
    /// The stage's `LIDB` and `statedTarget.hb`.
    pub lidb: i32,
    pub stated_hb: u32,
    /// `T2TAU`: the stage's `TAU` (the smallness test's number of combinations).
    pub tau: u32,
}

/// The attention sub-proof's plan (`struct AttentionSubProof`, through `plan()`).
#[derive(Default)]
pub struct AttentionSubProof {
    pub a: AFork,
    pub fs: HForest,
    pub input: AttentionSubProofInputs,
    pub seam: AttentionSeam,
    pub ns: u32,
    pub n_msg: usize,
    pub n_lin: usize,
    pub nc: usize,
    /// `NP`: pairs (layer, query head a).
    pub np: usize,
    pub n_krp: usize,
    pub n_kfp: usize,
    pub own: AttentionRounds,
    pub n_w: u64,
    pub n_claim: u32,
}

impl AttentionSubProof {
    /// `AttentionSubProof::holds`.
    pub fn holds(c: &ACall, seg: i32) -> bool {
        c.segs.contains(&seg)
    }

    /// `AttentionSubProof::npOf`.
    pub fn np_of(c: &ACall, seg: i32) -> usize {
        c.pcs.iter().filter(|p| p.seg == seg).count()
    }

    /// `AttentionSubProof::plan()`.
    pub fn plan(&mut self) -> Result<()> {
        if self.input.hb == 0 {
            return Err(Refusal::named("hid-hb"));
        }
        if self.input.a_o == 0 {
            return Err(Refusal::named("hid-a-owner-uses"));
        }
        if self.a.cf.ty != (1u128 << (1 + LBZ)) {
            return Err(Refusal::named("internal-a-Ty"));
        }
        self.fs = afork_shape_hid(&mut self.a, self.input.lidb)?;
        let c = self.a.cf.clone();
        let t = self.a.t;
        let k_part = self.a.k_as / c.n_as;
        self.nc = self.a.calls.len();
        self.np = (self.a.lam * self.a.ha) as usize;
        // The range check's matrices and their cells.
        let mut m: Vec<TMat> = Vec::new();
        let mut mat = |name: String, mm: u64, k: u64, kind: i32, mid: u64, wp: u32| {
            let mut x = TMat::default();
            x.name = name;
            x.m = mm;
            x.k = k;
            x.kind = kind;
            x.a_id = mid;
            x.wp = wp;
            if kind == 1 {
                x.foreign = 0;
            }
            m.push(x);
        };
        for q in 0..c.n_as {
            mat(format!("as{}", q), 1u64 << c.lm_s, k_part, 0, self.input.gid as u64 * 256 + q, self.input.wp_s);
        }
        mat(
            String::from("ah"),
            c.wc_h * t,
            self.a.fill_h / c.wc_h,
            0,
            self.input.gid as u64 * 256 + c.n_as,
            self.input.wp_h,
        );
        mat(
            String::from("ao"),
            c.wc_o * t,
            self.a.fill_o / c.wc_o,
            0,
            self.input.gid as u64 * 256 + c.n_as + 1,
            self.input.wp_o,
        );
        mat(
            String::from("bA"),
            1u64 << c.lmb,
            self.a.kb_a,
            0,
            self.input.gid as u64 * 256 + c.n_as + 2,
            self.input.wp_b_a,
        );
        mat(
            String::from("qa"),
            c.wc_q * t,
            self.a.fill_q / c.wc_q,
            1,
            self.input.mid_q,
            self.input.wp_q,
        );
        if c.n_as + 4 > 256 {
            return Err(Refusal::named("hid-a-fold-list"));
        }
        self.seam.shape(
            m,
            self.input.tau,
            self.input.col0_q,
            self.input.kt_o,
            self.input.a_o,
            self.input.lidb,
        )?;
        // Count the slots (msg).
        let lt = c.lt;
        let lam = self.a.lam;
        let mut msg = 0usize;
        let mut sum_np = 0usize;
        msg += forest_elems(&self.fs);
        self.n_krp = 0;
        self.n_kfp = 0;
        self.own = AttentionRounds::default();
        for k in &self.a.calls {
            if k.kind == "KR" {
                for s in [S_RM, S_RD] {
                    if Self::holds(k, s) {
                        self.n_krp += 1;
                        msg += 3;
                    }
                }
            }
            if k.kind == "KFD" {
                for s in [S_FM, S_FD] {
                    if Self::holds(k, s) {
                        self.n_kfp += 1;
                        let np = Self::np_of(k, s);
                        sum_np += np;
                        msg += (7 + sc3_slots(self.nv_kf(s), np)) as usize;
                        self.own.score.push((self.nv_kf(s) as u32, np as u32));
                    }
                }
            }
        }
        msg += 7 + lt as usize + sc3_slots(self.nv_e(), self.np) as usize;
        msg += 2 + sc3_slots(self.nv_vm(), self.np) as usize + sc3_slots(self.nv_vd(), self.np) as usize;
        msg += self.np
            + sc3_slots(self.nv_f(), self.np) as usize
            + sumcheck_slots_degrees(&self.scd_degrees(), (lam as usize + self.np * lt as usize) as u64, lt + 1) as usize
            + sc3_slots(self.nv_h(), self.np) as usize;
        msg += self.seam.small_elems();
        self.n_msg = msg;
        // Count the claims (nLin).
        {
            let seg_h = c.wc_h;
            let seg_o = (c.wc_o * t) >> c.la;
            let seg_q = (c.wc_q * t) >> c.la;
            let _ = (seg_h, seg_o, seg_q);
            self.n_lin = super::lookup::forest_lins(&self.fs)
                + 3 * self.n_krp
                + (6 * self.n_kfp + 2 * sum_np)
                + (5 + lt as usize + 2 * self.np)
                + 1
                + (1 + 4 * self.np)
                + (4 * self.np + lam as usize + self.np * lt as usize)
                + 3
                + (self.n_kfp + 5 + 1);
            if self.seam.tl.nm != c.n_as as usize + 4 {
                return Err(Refusal::named("internal-a-claim-count"));
            }
            let reads = 3 * c.n_as as usize
                + (self.n_kfp + 6) * seg_h as usize
                + seg_o as usize
                + (2 * self.n_kfp + 5) * seg_q as usize
                + 3;
            self.n_lin += self.seam.tl.lins(reads);
            self.own.rows = self.n_lin as u64 + self.seam.tl.equations(reads);
        }
        self.own.lt = lt as u32;
        self.own.lgk = c.lgk as u32;
        self.own.pairs = self.np as u32;
        self.own.lam = lam as u32;
        self.own.plane_messages = self.n_krp as u32;
        self.own.e = self.nv_e() as u32;
        self.own.value_m = self.nv_vm() as u32;
        self.own.value_d = self.nv_vd() as u32;
        self.own.attained = self.nv_f() as u32;
        self.own.bits = self.nv_h() as u32;
        if msg as u64 >= (1u64 << 30) {
            return Err(Refusal::named("hid-a-slots"));
        }
        self.n_w = (self.a.table_words() / WPE) as u64;
        self.seam.plan(self.n_w, self.input.hb, self.input.stated_hb)?;
        self.ns = msg as u32;
        Ok(())
    }

    /// `nvKF(seg)`.
    pub fn nv_kf(&self, seg: i32) -> i32 {
        if seg == S_FM {
            self.a.cf.lgk + 2 * self.a.ln_t - 1 + self.a.cf.ldh
        } else {
            self.a.cf.lgk + self.a.ln_t + self.a.cf.ldh
        }
    }

    /// `nvE()`.
    pub fn nv_e(&self) -> i32 {
        self.a.cf.lgk + self.a.cf.lt
    }

    /// `nvVM()`.
    pub fn nv_vm(&self) -> i32 {
        self.a.cf.lgk + 2 * self.a.ln_t - 1 + self.a.cf.l_b
    }

    /// `nvVD()`.
    pub fn nv_vd(&self) -> i32 {
        self.a.cf.lgk + self.a.ln_t + self.a.cf.l_b
    }

    /// `nvF()`.
    pub fn nv_f(&self) -> i32 {
        self.a.cf.lt + self.a.cf.lgk + self.a.cf.ldh
    }

    /// `nvH()`.
    pub fn nv_h(&self) -> i32 {
        self.a.cf.lt + self.a.cf.lgk + 4
    }

    /// `hsScd()`.
    pub fn hs_scd(&self) -> u64 {
        2 * self.a.cf.lt as u64 + self.a.cf.lgk as u64
    }

    /// `scdDegrees()`.
    pub fn scd_degrees(&self) -> Vec<i32> {
        let lt = self.a.cf.lt;
        let lgk = self.a.cf.lgk;
        (0..self.hs_scd() as i32)
            .map(|j| if j < lt { 2 } else if j < lt + lgk { lt + 2 } else { lt + 1 })
            .collect()
    }

    /// The chain rounds that follow commit point `moment` (`rounds` in C++).
    pub fn plan_rounds_for(&self, p: &mut Plan, moment: u32) -> Result<()> {
        let where_ = format!("attention {}", self.input.gid);
        if moment == 0 {
            super::lookup::forest_plan(p, &format!("{}, look-up", where_), &self.fs);
            plan_attention_own(p, &where_, &self.own);
        }
        if moment >= 1 {
            self.seam
                .tl
                .plan_rounds(p, &format!("{}, smallness test", where_), moment - 1)?;
        }
        if moment == 2 {
            plan_attention_end(p, &where_, &self.own);
        }
        Ok(())
    }
}
