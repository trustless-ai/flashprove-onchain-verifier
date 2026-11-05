//! Plans the layer sub-proof G_g of each layer group, ported from
//! `verifier/src/vf_layers_plan.inc` (and the `readsZ`/`readsR`/read-list block of `runStage()`
//! that it reads). It reads no word of a proof. `vf_layers_check.inc` checks G_g with the plan; if
//! its own counts differ, the call ends NOT CHECKED.
//!
//! `tl`: G_g's approximate range check (the "smallness test"). `fp`, `tp`: the committed arrays
//! and their shape records. `n_u`: lengths of U1 to U3, vectors over E. `rounds`: adds to a hash
//! chain's plan G_g's own rounds after one commit point (`moment`).

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::numbers::blocks::plan_bat_sigma;
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::Plan;
use crate::refusal::{Refusal, Result};

use super::common::WPE;
use super::layers_rounds::{plan_layer_own, LayerRounds};
use super::lookup::{forest_elems, forest_lins, forest_plan, HForest};
use super::matrices::{Tail, TMat};
use super::norm_digit_rows::{led_lines, led_no, led_np, led_ns};
use super::packing::same_place_f;
use super::segment::{t2_plan, N2, Tail2};
use super::smallness::{HTailF2, T2Foreign};
use super::stage_layout::{Hdr, Lay};
use super::sumcheck::{layer_slots, sumcheck_slots, tsc_slots, RoundForm};
use super::weights_merge::ws_fork_slots;
use super::engine::{trim_l, HFork, HTree};

/// The evaluation tables a layer sub-proof commits to (its U3), in order: for each matrix, the
/// points where it is read (`readsZ`, `readsR`). Letters: f = af, d = ad, r = ar, q = qa,
/// Q = a short table of qa_g, i = xb_g, o = xb_(g+1).
#[derive(Clone, Debug, Default)]
pub struct Reads {
    pub tsc_calls: Vec<String>,
    pub af: Vec<String>,
    pub qa: Vec<String>,
    pub xi: Vec<String>,
    pub xo: Vec<String>,
    pub ad: Vec<String>,
    pub ar: Vec<String>,
    pub qs: Vec<String>,
}

fn reads_z(s: &str) -> &'static str {
    match s {
        "G" | "U" | "V" | "CN1" | "CN2" => "df",
        "O" => "fiQ",
        "D" => "fo",
        "XR" => "d",
        "LR" => "dr",
        "LT" | "DD" | "ROW" | "LH" | "SEL" | "MR" | "L3" | "CLR" => "r",
        "CQK" | "CV" => "fq",
        _ => "f",
    }
}

fn reads_r(s: &str, p3: bool) -> &'static str {
    match s {
        "N1" => "rfi",
        "N2" => "rf",
        "QK" => "d",
        _ if p3 && (s == "G" || s == "U" || s == "XR") => "rd",
        _ if p3 && (s == "D" || s == "DD" || s == "MR") => "r",
        _ => "",
    }
}

fn has(s: &str, c: char) -> bool {
    s.contains(c)
}

fn any(v: &[String], c: char) -> bool {
    v.iter().any(|s| has(s, c))
}

/// The read lists of `runStage()` before the plan includes (cp_verify.cpp:1996-2079).
pub fn reads_of(y: &Lay, p3: bool) -> Reads {
    let mut zs: Vec<String> = vec![String::new(); y.calls.len()];
    let mut rs: Vec<String> = vec![String::new(); y.calls.len()];
    for q in 0..y.calls.len() {
        for s in &y.calls[q].segs {
            zs[q].push_str(reads_z(&s.name));
            rs[q].push_str(reads_r(&s.name, p3));
        }
    }
    let mut r = Reads::default();
    for q in 0..y.calls.len() {
        if !rs[q].is_empty() {
            r.tsc_calls.push(y.calls[q].c.name.clone());
        }
    }
    // The long tables: af, qa, xb_in, xb_out; at Z, Z_V, Y and (af) Z_a, Z_b.
    {
        let long: [(&mut Vec<String>, char, bool, bool); 4] = [
            (&mut r.af, 'f', true, true),
            (&mut r.qa, 'q', false, false),
            (&mut r.xi, 'i', true, false),
            (&mut r.xo, 'o', false, false),
        ];
        for (v, c, zv, zab) in long {
            if any(&zs, c) {
                v.push(String::from("Z"));
            }
            if zv {
                v.push(String::from("Z_V"));
            }
            if any(&rs, c) {
                v.push(String::from("Y"));
            }
            if zab {
                v.push(String::from("Z_a"));
                if p3 {
                    v.push(String::from("Z_b"));
                }
            }
        }
    }
    // The short tables, in the order ad_g, ar_g, qa_g.
    {
        let short: [(&mut Vec<String>, char, bool); 3] =
            [(&mut r.ad, 'd', false), (&mut r.ar, 'r', true), (&mut r.qs, 'Q', false)];
        for (v, c, pv) in short {
            if any(&zs, c) {
                v.push(String::from("zt"));
            }
            if pv {
                v.push(String::from("P_V"));
                v.push(String::from("r_tV"));
            }
            if any(&rs, c) {
                v.push(String::from("rt"));
            }
        }
    }
    r
}

/// `t2SameShape` (vf_subproof_segment.h:24-26).
pub fn t2_same_shape(a: &N2, at: &HTree, b: &N2, bt: &HTree) -> bool {
    at.r == bt.r
        && at.k == bt.k
        && a.ec == b.ec
        && a.a == b.a
        && a.p == b.p
        && (!a.p || a.shape.same(&b.shape))
}

/// A layer sub-proof's plan (`HPlan2`, vf_layers_plan.inc:13-23). `x`: the sizes of the rounds
/// after one commit point; `plan_layer_moment()` uses them.
#[derive(Clone, Debug)]
pub struct HPlan2 {
    pub tl: HTailF2,
    pub fp: HFork,
    pub tp: Tail2,
    pub n_u: [u64; 3],
    /// Message slots, one per scalar sent.
    pub ns: u32,
    /// Those taken (equal).
    pub used: u32,
    /// Claims on the weights.
    pub n_cl: usize,
    /// The sub-proof's claims, all linear.
    pub n_lin: usize,
    /// `n_lin` plus the range check's equations; one element's powers batch them all.
    pub n_batched: u64,
    pub lam_s: i32,
    /// The sizes of the rounds after a commit point.
    pub x: LayerRounds,
    /// The name in the plan's prints ("G<g>").
    pub where_: String,
    pub g: u64,
    pub claims: u64,
}

/// The layer plans and the number of placement-record comparisons (`borderCmpF`).
#[derive(Clone, Debug, Default)]
pub struct LayerPlans {
    pub hid: Vec<HPlan2>,
    pub border_cmp: usize,
}

/// The inputs of `plan_layers`: the stage's header and layout, the group matrices, and what
/// `runStage()` read from the files (`reads_of`) and the frame (`lk_w`, `lidb`, `hb`).
pub struct LayerPlanInputs<'a> {
    pub h: &'a Hdr,
    pub y: &'a Lay,
    pub tails: &'a [Tail],
    pub reads: &'a Reads,
    /// `PS.frame.block_log`.
    pub lk_w: u32,
    /// `state.lidb`.
    pub lidb: i32,
    /// `statedTarget.hb - POW`.
    pub hb: u32,
    /// `statedTarget.hb`, the value of the parameter file's line `sec`.
    pub stated_hb: u32,
    /// The residual stream's limbs (`state.residual_stream_limbs`).
    pub limbs: i32,
}

/// The sizes that the plan reads off the layout before its per-group loop (cp_verify.cpp:2087-2093).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LayerPlanSizes {
    pub l_ni: i32,
    pub mu_v: i32,
    pub mu_h: i32,
    pub mu_h2: i32,
    /// The length of U3, before each group's extra table (`wW`).
    pub ww: u64,
}

/// `lNI`, `muV`, `muH`, `muH2` and `wW` (cp_verify.cpp:2087-2093).
pub fn plan_sizes(y: &Lay, h: &Hdr, rd: &Reads) -> LayerPlanSizes {
    let l_ni = ceil_log2(y.ni) as i32;
    let mu_v = l_ni + y.l_pd + h.lt as i32;
    let mu_h = h.ll as i32 + y.l_pf + h.lt as i32;
    let mu_h2 = h.ll as i32 - 1 + y.lfe + h.lt as i32;
    let t = y.t;
    let gs_af = y.filled[0] * t >> h.la;
    let gs_xb = y.xb_filled * t >> h.la;
    let gs_qa = y.filled[3] * t >> h.la;
    let ww = WPE as u64
        * (rd.af.len() as u64 * gs_af
            + rd.qa.len() as u64 * gs_qa
            + (rd.xi.len() + rd.xo.len()) as u64 * gs_xb
            + rd.ad.len() as u64 * y.filled[1]
            + rd.ar.len() as u64 * y.filled[2]
            + rd.qs.len() as u64 * y.filled[3]
            + 3 * y.kbm);
    LayerPlanSizes { l_ni, mu_v, mu_h, mu_h2, ww }
}

/// `vf_layers_plan.inc:26-182`: the plan of every layer group. `p3` follows `h.ne`.
pub fn plan_layers(inp: &LayerPlanInputs<'_>) -> Result<LayerPlans> {
    let h = inp.h;
    let y = inp.y;
    let p3 = h.ne > 0;
    let d = h.d;
    let fe = h.fe;
    let lam = y.lam;
    let ngr = y.ngr;
    let nn = y.nn;
    let ni = y.ni;
    let dq = y.dq;
    let la = h.la;
    let lt = h.lt;
    let ls = y.ls;
    let l_pd = y.l_pd;
    let l_pf = y.l_pf;
    let l_fe = y.lfe;
    let ll = h.ll;
    let ne = h.ne;
    let lam_m = y.lam_m;
    let rd = inp.reads;
    if y.ngr as usize != inp.tails.len() {
        return Err(Refusal::internal("internal-g-tail-count"));
    }
    let sz = plan_sizes(y, h, rd);
    let l_ni = sz.l_ni;
    let mu_v = sz.mu_v;
    let mu_h = sz.mu_h;
    let mu_h2 = sz.mu_h2;
    let ww = sz.ww;
    let i_ad = y.parts[0] as usize;
    let i_ar = i_ad + y.parts[1] as usize;
    let i_b = i_ar + 1;
    let i_qa = i_b + 1;
    let i_xo = i_qa + 1;
    let i_xi = i_xo + 1;

    let mut out = LayerPlans::default();
    for g in 0..ngr {
        let mut mats: Vec<TMat> = inp.tails[g as usize].mats.clone();
        let mut tx_of = vec![-1i32; mats.len()];
        let mut ft: Vec<T2Foreign> = Vec::new();
        let mut a_tx: Vec<u32> = Vec::new();
        for mu in 0..mats.len() {
            if mats[mu].kind == 0 && (mu == i_xo || mu == i_qa) {
                tx_of[mu] = a_tx.len() as i32;
                a_tx.push(2);
            } else if mats[mu].kind == 1 {
                let mut f = T2Foreign::default();
                f.name = format!("PXf{}", ft.len());
                f.k = mats[mu].k;
                f.a = 2;
                f.m = mats[mu].m;
                f.wp = mats[mu].wp;
                mats[mu].foreign = ft.len() as i32;
                mats[mu].tt_off = 0;
                ft.push(f);
            } else if mats[mu].kind == 2 {
                return Err(Refusal::named("internal-weight-matrix"));
            }
        }
        let mut tl = HTailF2::new();
        let has_u = [false, false, true, false];
        tl.shape(&mats, &tx_of, &ft, has_u, h.tau, inp.lidb)?;
        let fo: &HForest = &y.fo;
        let mut msg = forest_elems(fo) as u64;
        let n_t = if rd.tsc_calls.is_empty() { 0u64 } else { 1 };
        let lam_s = {
            let wi = ceil_log2(lam) as i32;
            let mut tot = 4 * (1u64 << (wi + ceil_log2(d) as i32))
                + (1u64 << (wi + ceil_log2(dq) as i32))
                + (1u64 << (wi + ceil_log2(h.f) as i32))
                + 2 * (1u64 << wi);
            if p3 {
                let wm = ceil_log2(lam_m) as i32;
                let le = ceil_log2(ne) as i32;
                tot += (1u64 << (wm + ceil_log2(d) as i32))
                    + (1u64 << wm)
                    + 2 * (1u64 << (wm + le))
                    + lam_m * (2 * (1u64 << (le + ceil_log2(d) as i32)) + (1u64 << (le + ceil_log2(fe) as i32)));
            }
            ceil_log2(tot) as i32
        };
        let n_cl = (6 * lam + if p3 { 4 * lam_m } else { 0 } + if g == 0 { 1 } else { 0 }) as usize;
        let limbs = inp.limbs;
        let lin = forest_lins(fo) as u64
            + 3
            + (2 + (led_no(limbs) + led_ns(limbs) + led_lines(limbs)) as u64 * ni)
            + if n_t != 0 {
                nn * lam + if p3 { lam_m * (1 + ne) } else { 0 }
            } else {
                0
            }
            + 3
            + if p3 { 3 } else { 0 }
            + if p3 { lam_m } else { 0 }
            + 3
            + if g == 0 { 1 } else { 0 }
            + 3
            + 1;
        let n_x4 = (rd.af.len() as u64 * y.parts[0] * (y.mrow[0] >> la)
            + rd.qa.len() as u64 * (y.mrow[3] >> la)
            + (rd.xi.len() + if g == 0 { 1 } else { 0 } + rd.xo.len()) as u64 * (y.mxb >> la)
            + rd.ad.len() as u64 * y.parts[1] * (y.mrow[1] >> lt)
            + rd.ar.len() as u64 * (y.mrow[2] >> lt)
            + rd.qs.len() as u64 * (y.mrow[3] >> lt)
            + 3) as usize;
        let n_lin = lin as usize + tl.lins(n_x4);
        let n_batched = n_lin as u64 + tl.equations(n_x4);

        let x = LayerRounds {
            lt: lt,
            ls: ls as u32,
            l_ni: l_ni as u32,
            l_pd: l_pd as u32,
            ll: ll,
            l_pf: l_pf as u32,
            l_fe: l_fe as u32,
            lam_s: lam_s as u32,
            lk_w: inp.lk_w,
            ni,
            ns: led_ns(limbs) as u64,
            np: led_np(limbs) as u64,
            no: led_no(limbs) as u64,
            with_terms: n_t != 0,
            shown_by_the_terms: if n_t != 0 {
                nn * lam + if p3 { lam_m * (1 + ne) } else { 0 }
            } else {
                0
            },
            never_sent: 1 + if p3 { lam_m } else { 0 },
            weight_claims: (n_cl as u64) - if g == 0 { 1 } else { 0 },
            first_group: g == 0,
            routed: p3,
        };
        msg += led_ns(limbs) as u64 * ni + layer_slots(mu_v) + led_np(limbs) as u64 * ni;
        msg += tsc_slots(lt as i32, (led_no(limbs) as u64) * ni, 2, 0);
        if n_t != 0 {
            msg += tsc_slots(
                lt as i32,
                nn * lam + if p3 { lam_m * (1 + ne) } else { 0 },
                1,
                0,
            );
        }
        msg += sumcheck_slots(
            RoundForm::Sum2,
            lam_s,
            2 + 1 + if p3 { lam_m } else { 0 } + n_cl as u64 - if g == 0 { 1 } else { 0 },
            2,
            0,
        );
        msg += layer_slots(mu_h)
            + if p3 { layer_slots(mu_h2) } else { 0 }
            + if g == 0 { 1 } else { 0 }
            + ws_fork_slots(inp.lk_w as i32)
            + tl.small_elems() as u64;

        let mut n_u = [0u64; 3];
        n_u[2] = ww / WPE as u64
            + if g == 0 {
                mats[i_xi].k * (mats[i_xi].m >> la)
            } else {
                0
            };
        let mut fp = HFork::default();
        fp.g = format!("G{}:", g);
        let mut tp = Tail2::default();
        tl.add_trees(&mut fp, &mut tp, n_u, &a_tx, inp.hb, inp.stated_hb)?;
        t2_plan(&mut fp, &mut tp)?;
        if tl.ix.ft.len() != if g > 0 { 1 } else { 0 } {
            return Err(Refusal::named("internal-g-owner-shape"));
        }
        if g > 0 {
            let o = &out.hid[g as usize - 1];
            let otx = match o.tl.ix.tx.last() {
                Some(&x) => x as usize,
                None => return Err(Refusal::named("internal-g-owner-shape")),
            };
            let ift = match tl.ix.ft.first() {
                Some(&x) => x as usize,
                None => return Err(Refusal::named("internal-g-owner-shape")),
            };
            if !t2_same_shape(&o.tp.nt[otx], &o.fp.trees[otx], &tp.nt[ift], &fp.trees[ift]) {
                return Err(Refusal::named("internal-g-owner-shape"));
            }
        }
        tl.owner_is(g as i32);
        if g > 0 {
            let o = &mut out.hid[g as usize - 1];
            tl.border_means(0, g as i32 - 1, (o.tl.pk_mat.len() + o.tl.ix.tx.len()) as i32 - 1)?;
            let df = same_place_f(o.tl.own_entry("stream")?, &tl.pl_for[0]);
            if !df.is_empty() {
                return Err(Refusal::internal(&format!("internal-g-owner-place-{}", df)));
            }
            out.border_cmp += 1;
        }
        if msg >= (1u64 << 30) {
            return Err(Refusal::named("hid-g-slots"));
        }
        let where_ = format!("G{}", g);
        out.hid.push(HPlan2 {
            tl,
            fp,
            tp,
            n_u,
            ns: msg as u32,
            used: msg as u32,
            n_cl,
            n_lin,
            n_batched,
            lam_s,
            x,
            where_,
            g,
            claims: n_batched,
        });
        trim_l(&mut out.hid[g as usize].fp);
    }
    Ok(out)
}

/// The rounds after commit point `moment` of G_g (the C++ `P.rounds` lambda,
/// vf_layers_plan.inc:111-119).
pub fn plan_layer_moment(
    p: &mut Plan,
    plan: &HPlan2,
    look: &HForest,
    moment: u32,
) -> Result<()> {
    if moment == 0 {
        forest_plan(p, &format!("{}, look-up", plan.where_), look);
        plan_layer_own(p, &plan.where_, &plan.x);
        return Ok(());
    }
    plan.tl
        .plan_rounds(p, &format!("{}, smallness test", plan.where_), moment - 1)?;
    if moment == 2 {
        plan_bat_sigma(p, &format!("{}, claims", plan.where_), plan.claims);
    }
    Ok(())
}
