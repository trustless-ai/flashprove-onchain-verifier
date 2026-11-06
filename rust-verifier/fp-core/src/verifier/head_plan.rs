//! The plan of the output head's sub-proof H, ported from `verifier/src/vf_output_head_plan.inc`.
//! No proof is read here. It uses the layer plans (`hidPlans2`), the head's layout (`HLy`, built by
//! `build_hl`) and the stage's sizes, and produces the `HPlanH2` from which `vf_output_head_check`
//! reads H.

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::Plan;
use crate::refusal::{Refusal, Result};

use super::engine::{trim_l, HFork};
use super::head_rounds::{plan_head_end, plan_head_own, HeadRounds};
use super::layers_plan::{t2_same_shape, HPlan2};
use super::lookup::{forest_elems, forest_lins, forest_plane_cols, forest_plan, HForest};
use super::matrices::TMat;
use super::norm_digit_rows::{led_lines, led_no, led_np, led_ns};
use super::packing::same_place_f;
use super::segment::{t2_plan, Tail2};
use super::smallness::{HTailF2, T2Foreign};
use super::stage_context::Hl;
use super::stage_layout::{Hdr, Lay};
use super::sumcheck::{layer_slots, tsc_slots};
use super::weights_merge::ws_fork_slots;

/// The output head's plan (`HPlanH2`, vf_output_head_plan.inc:9-24).
#[derive(Clone, Debug)]
pub struct HPlanH2 {
    pub tl: HTailF2,
    pub fp: HFork,
    pub tp: Tail2,
    pub n_u: [u64; 3],
    pub ns: u32,
    pub n_msg: u64,
    pub n_lin: usize,
    /// The weight claims.
    pub n_cl: u64,
    /// The sizes of H's rounds.
    pub own: HeadRounds,
    pub lam_s: i32,
}

pub struct HeadPlanInputs<'a> {
    pub h: &'a Hdr,
    pub y: &'a Lay,
    pub hl: &'a Hl,
    pub hid: &'a [HPlan2],
    /// `PS.frame.block_log`.
    pub lk_w: u32,
    pub lidb: i32,
    /// `statedTarget.hb - POW`.
    pub hb: u32,
    /// `statedTarget.hb`.
    pub stated_hb: u32,
    pub limbs: i32,
}

impl HPlanH2 {
    /// The rounds after commit point `moment` (the C++ `P.rounds` lambda,
    /// vf_output_head_plan.inc:131-143).
    pub fn plan_moment(&self, p: &mut Plan, look: &HForest, moment: u32) -> Result<()> {
        let where_ = "head";
        if moment == 0 {
            forest_plan(p, &format!("{}, look-up", where_), look);
            plan_head_own(p, where_, &self.own);
        }
        if moment >= 1 {
            self.tl
                .plan_rounds(p, &format!("{}, smallness test", where_), moment - 1)?;
        }
        if moment == 2 {
            plan_head_end(p, where_, &self.own);
        }
        Ok(())
    }
}

/// `vf_output_head_plan.inc:26-145`.
pub fn plan_head(inp: &HeadPlanInputs<'_>) -> Result<HPlanH2> {
    let h = inp.h;
    let y = inp.y;
    let hl = inp.hl;
    let ngr = y.ngr;
    let la = h.la;
    let lt = h.lt;
    let l_pd = y.l_pd;
    let vv = h.v;
    let t = y.t;
    if inp.hid.len() as u64 != ngr {
        return Err(Refusal::internal("internal-h-plan-count"));
    }
    let lk_w = inp.lk_w;
    let mut p = HPlanH2 {
        tl: HTailF2::new(),
        fp: HFork::default(),
        tp: Tail2::default(),
        n_u: [0; 3],
        ns: 0,
        n_msg: 0,
        n_lin: 0,
        n_cl: 1,
        own: HeadRounds::default(),
        lam_s: 0,
    };
    p.fp.g = String::from("H:");
    if ceil_log2(vv) > lk_w {
        return Err(Refusal::named("hid-vocab-cols"));
    }
    if hl.fs.names.len() != hl.calls.len()
        || hl.fs.pub_.len() != hl.fs.nt as usize
        || hl.kb != forest_plane_cols(&hl.fs, h.lmbh as i32)?
    {
        return Err(Refusal::named("internal-h-forest"));
    }
    let gid_h = 1 + ngr;
    let mut mats: Vec<TMat> = Vec::new();
    {
        let mut req = |name: String, m: u64, k: u64, wp: u32| {
            let mut mat = TMat::default();
            mat.name = name;
            mat.m = m;
            mat.k = k;
            mat.wp = wp;
            mat.a_id = gid_h * 256 + mats.len() as u64;
            mats.push(mat);
        };
        for q in 0..h.nhf {
            req(format!("hf{}", q), hl.m, hl.k, 0);
        }
        req(String::from("hd"), hl.md, hl.kd, 0);
        req(String::from("hr"), hl.mr, hl.kr, 0);
        req(String::from("bH"), 1u64 << h.lmbh, hl.kb, 0);
        req(String::from("xbL"), y.mxb, y.kxb, 0);
    }
    {
        let last = mats.len() - 1;
        mats[last].kind = 1;
        mats[last].foreign = 0;
        mats[last].tt_off = 0;
        mats[last].a_id = inp.hid[ngr as usize - 1].tl.mats[i_xo(y)].a_id;
    }
    let fx = T2Foreign { name: String::from("PXf0"), k: y.kxb, a: 2, m: y.mxb, wp: 0 };
    let has_u = [false, false, true, false];
    let tx_of = vec![-1i32; mats.len()];
    p.tl.shape(&mats, &tx_of, &[fx], has_u, h.tau, inp.lidb)?;
    let mut msg = forest_elems(&hl.fs) as u64;
    let lam_s = l_pd;
    p.lam_s = lam_s;
    let mu_vh = l_pd + lt as i32;
    if mu_vh < 9 {
        return Err(Refusal::named("shape-product-layer-H"));
    }
    let limbs = inp.limbs;
    msg += p.tl.small_elems() as u64
        + led_ns(limbs) as u64
        + layer_slots(mu_vh)
        + led_np(limbs) as u64
        + tsc_slots(lt as i32, led_no(limbs) as u64, 2, 0)
        + tsc_slots(lt as i32, 2, 2, 0)
        + tsc_slots(lt as i32, 2, 2, lam_s)
        + ws_fork_slots(lk_w as i32);
    // An evaluation table sums runs of a matrix's rows under public weights. GSx: the size of
    // xbL's.
    let gs_x = y.kxb * (y.mxb >> la);
    let nhf_z = 2u64;
    p.n_u[2] = nhf_z * (hl.filled * t >> la) + 2 * gs_x + 2 * hl.filld + 6 * hl.fillr + 3 * hl.kb;
    let reads_h = (nhf_z * h.nhf as u64 * (hl.m >> la)
        + 2 * (hl.md >> lt)
        + 6 * (hl.mr >> lt)
        + 3
        + 2 * (y.mxb >> la)) as usize;
    p.n_lin = forest_lins(&hl.fs) as usize
        + 3
        + (1 + 1 + led_no(limbs) + led_ns(limbs) + led_lines(limbs)) as usize
        + 3
        + 1
        + 4
        + 3
        + 2
        + 1
        + p.tl.lins(reads_h);
    p.tl.add_trees(&mut p.fp, &mut p.tp, p.n_u, &[], inp.hb, inp.stated_hb)?;
    if p.tp.nt.len() != 1 + p.tl.pk_mat.len() + 2 + 1 {
        return Err(Refusal::named("internal-h-tree-list"));
    }
    t2_plan(&mut p.fp, &mut p.tp)?;
    {
        let o = &inp.hid[ngr as usize - 1];
        let otx = match o.tl.ix.tx.last() {
            Some(&x) => x as usize,
            None => return Err(Refusal::named("internal-h-owner-TX")),
        };
        let ift = p.tl.ix.ft[0] as usize;
        if !t2_same_shape(&o.tp.nt[otx], &o.fp.trees[otx], &p.tp.nt[ift], &p.fp.trees[ift]) {
            return Err(Refusal::named("internal-h-owner-shape"));
        }
        p.tl.border_means(
            0,
            ngr as i32 - 1,
            (o.tl.pk_mat.len() + o.tl.ix.tx.len()) as i32 - 1,
        )?;
        let df = same_place_f(o.tl.own_entry("stream")?, &p.tl.pl_for[0]);
        if !df.is_empty() {
            return Err(Refusal::internal(&format!("internal-h-owner-place-{}", df)));
        }
    }
    if msg >= (1u64 << 30) {
        return Err(Refusal::named("hid-h-slots"));
    }
    p.n_msg = msg;
    p.own = HeadRounds {
        lt,
        l_pd: l_pd as u32,
        lk_w,
        sums: led_ns(limbs) as u32,
        products: led_np(limbs) as u32,
        row_values: led_no(limbs) as u32,
        rows: p.n_lin as u64
            + {
                let n_x4 = reads_h;
                p.tl.equations(n_x4)
            },
    };
    p.ns = msg as u32;
    trim_l(&mut p.fp);
    Ok(p)
}

/// The index of `xbO` among a layer group's matrices (the last border array; see `build_tails`).
fn i_xo(y: &Lay) -> usize {
    (y.parts[0] + y.parts[1]) as usize + 3
}
