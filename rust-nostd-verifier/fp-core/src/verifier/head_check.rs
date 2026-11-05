//! Checks H, the output head's sub-proof, ported from `verifier/src/vf_output_head_check.inc`
//! (the `runForkHidH2` lambda): the final norm, the logits and the acceptance policy on the
//! checked tokens. It reads the request's first hash chain through [`Tr`]; the segment calls that
//! C++ reaches through `currentSegment` go through [`AttentionSegment`].
//!
//! For a hidden value x the prover sends ("shows") `x` plus a public factor times a mask entry,
//! whose number is x's message slot. Sumchecks are masked sumchecks. Every other check is a claim
//! (`lin`): an affine form in hidden values and table entries must be 0.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::refusal::{Refusal, Result};

use super::attention_check::AttentionSegment;
use super::attention_shape::{cut_last, ten_cell};
use super::common::{eq_tab, fint, order_default};
use super::engine::{fill_l, layer_object, read_product_level_rounds, Aff, HFork};
use super::head_plan::HPlanH2;
use super::layers_plan::HPlan2;
use super::lookup::{forest_join, forest_pad, forest_plane_lins, forest_phi_b, forest_phi_p, u_ent, HFun};
use super::norm_digit_rows::{led_carry5, led_lines5, led_mu, led_no, led_np, led_nr, led_nrh, led_ns, led_products5, row5, Row5, EXC};
use super::packing::e_scale;
use super::segment::eq_low;
use super::stage_layout::{Hdr, Lay};
use super::sumcheck::{psc_ends, psc_row, round_in, tsc_in, tsc_rounds, TokenSumcheckState, RoundForm};
use super::transcript::{tr_batch, tr_point, RoundName, Tr};
use super::weights_layout::{ws_fork_end, WsClaim, WsFac, WsForkOut, WsLay};
use super::weights_merge::ws_fork_lin;

fn ei(v: i64) -> E {
    E::from_base(crate::field::ext::F::from_u64(fint(v)))
}

fn pw(k: u32) -> E {
    ei(1i64 << k)
}

/// `LEDG` (vf_norm_digit_rows.h:50): offset and length of c, b, u, k, z, zs after the norm's
/// digits.
const LEDG: [(u64, usize); 6] = [(0, 5), (5, 1), (6, 5), (11, 5), (16, 2), (18, EXC)];

/// `BIGH` (vf_norm_digit_rows.h:51).
const BIGH: u64 = 1u64 << 37;

fn zl_h(c: &super::stage_layout::CallD) -> &[E] {
    &c.c.zk
}

fn zt_h(c: &super::stage_layout::CallD) -> &[E] {
    &c.c.zk[c.l_j as usize..]
}

fn call_of_h<'a>(hl: &'a super::stage_context::Hl, sn: &str) -> Result<&'a super::stage_layout::CallD> {
    for c in &hl.calls {
        for s in &c.segs {
            if s.name == sn {
                return Ok(c);
            }
        }
    }
    Err(Refusal::internal(&format!("internal-segment-{}", sn)))
}

fn tab_at(tab: &BTreeMap<String, u64>, n: &str) -> Result<u64> {
    tab.get(n)
        .copied()
        .ok_or_else(|| Refusal::internal(&format!("internal-table-{}", n)))
}

fn u3_at(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    t: u64,
    i: u64,
) -> Result<Aff> {
    match tab_len.get(&t) {
        Some(&len) if i < len => u_ent(f, i_u3, t + i),
        _ => Err(Refusal::internal(&format!(
            "{}internal-h-table-index",
            f.g
        ))),
    }
}

fn sum_e(v: &[E]) -> E {
    let mut s = E::zero();
    for &x in v {
        s = s + x;
    }
    s
}

/// `ewOf(sn)` over the head's calls.
fn ew_of(hl: &super::stage_context::Hl, sn: &str) -> Result<Vec<E>> {
    let c = call_of_h(hl, sn)?;
    let e = eq_tab(zl_h(c), c.l_j as usize);
    let s = c.seg(sn)?;
    let mut w = vec![E::zero(); s.n as usize];
    for x in 0..s.n as usize {
        w[x] = e[s.pos[x] as usize];
    }
    Ok(w)
}

/// `ewh(sn)` over the head's calls.
fn ewh(hl: &super::stage_context::Hl, ls: u32, s2: u64, sn: &str) -> Result<Vec<E>> {
    let c = call_of_h(hl, sn)?;
    let k = cut_last(zl_h(c), c.l_j as usize, ls as usize)?;
    let e = eq_tab(k.hi, k.nhi);
    let s = c.seg(sn)?;
    let mut w = vec![E::zero(); s.n as usize / s2 as usize];
    for xh in 0..w.len() {
        w[xh] = e[(s.pos[s2 as usize * xh] / s2) as usize];
    }
    Ok(w)
}

/// The inputs of the output head's check.
pub struct HeadCheckInputs<'a> {
    pub h: &'a Hdr,
    pub y: &'a Lay,
    pub hl: &'a super::stage_context::Hl,
    pub plan: &'a HPlanH2,
    pub hid: &'a [HPlan2],
    pub ws_lay: &'a WsLay,
    pub ngr: u64,
    pub lidb: i32,
    pub limbs: i32,
    /// The next token, received in the segment's plain scalars.
    pub y_tok: u32,
    /// The token checked at each covered position.
    pub win: &'a [u32],
    pub on: &'a [bool],
    pub on_c: &'a [bool],
    pub hrc: u64,
}

/// What the run hands the request frame.
pub struct HeadRunOut {
    pub wo: WsForkOut,
    pub nc: usize,
    pub nm: usize,
    pub n_claim: u32,
    pub n_slots: u32,
}

/// `runForkHidH2()` (vf_output_head_check.inc:21-646): the output head's whole check.
pub fn run_head(
    inp: &HeadCheckInputs<'_>,
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    gate: &mut dyn AttentionSegment,
    calls: &mut HashCalls,
) -> Result<HeadRunOut> {
    let h = inp.h;
    let y = inp.y;
    let hl = inp.hl;
    let hp = inp.plan;
    let vv = h.v;
    let t = y.t;
    let lt = h.lt;
    let la = h.la;
    let ls = y.ls as u32;
    let s2 = y.s2;
    let d = h.d;
    let l_pd = y.l_pd;
    let limbs = inp.limbs;
    f.g = String::from("H:");
    f.trees = hp.fp.trees.clone();
    fill_l(f);
    let mut t2 = hp.tp.clone();
    let mut tl = hp.tl.clone();
    let i_u3 = tl.ix.u[2] as u32;
    let mut l = hl.clone();
    for c in &mut l.calls {
        if c.kind == "FC" {
            c.c.tau = Some(y.tau_fc.clone());
        }
    }
    let nc = l.calls.len();
    f.slots(hp.ns);
    {
        let o = &inp.hid[inp.ngr as usize - 1];
        if o.tl.ix.tx.is_empty() || o.tl.k_tx.last() != Some(&y.kxb) {
            return Err(Refusal::named("internal-h-owner-TX"));
        }
    }
    let mut slot = 0u32;
    // The lookup calls run as one forest.
    let cl1: Vec<super::common::Call> = l.calls.iter().map(|c| c.c.clone()).collect();
    let mut g1 = forest_pad(f, tr, &cl1, &l.fs.pub_, &mut slot, inp.lidb, calls)?;
    for q in 0..l.calls.len() {
        l.calls[q].c.alpha = g1.alpha;
        l.calls[q].c.zk = g1.zk[q].clone();
    }
    let zl = super::attention_shape::last_of(&g1.zx, la as usize)?;
    for c in &l.calls {
        for i in 0..la as usize {
            let zk = &c.c.zk;
            if zk[zk.len() - la as usize + i] != zl[i] {
                return Err(Refusal::internal(&format!("{}internal-h-merged-point", f.g)));
            }
        }
    }
    // P_V: the point over the positions at which the norm's equations are tested.
    let pv = tr_point(tr, RoundName::Zero, lt as usize, calls)?;
    let half = ei(2).inv();
    let mut plain_pd = E::one();
    for _ in 0..l_pd {
        plain_pd = plain_pd * half;
    }
    let mu_vh = (l_pd + lt as i32) as usize;
    let ns_l = led_ns(limbs) as u64;
    let np_l = led_np(limbs) as u64;
    let no_l = led_no(limbs) as u64;
    let s_w = f.claims_in(tr, &mut slot, ns_l as u32)?;
    let gp = tr_batch(tr, ns_l as usize, calls)?;
    let wpl = {
        let mut c = Aff::default();
        for s in 0..ns_l {
            c = c + Aff::slot(s_w + s as u32) * (gp[s as usize] * plain_pd);
        }
        let mut rho = vec![half; l_pd as usize];
        rho.extend_from_slice(&pv);
        read_product_level_rounds(f, tr, &mut slot, mu_vh, &rho, &c, &order_default(mu_vh), calls)?
    };
    let s_pv = f.claims_in(tr, &mut slot, np_l as u32)?;
    let om_v = tr_batch(tr, np_l as usize, calls)?;
    let mut t_v = tsc_in(f, tr, &mut slot, &pv, lt as i32, no_l as u32, 2, calls)?;
    {
        let s0 = if limbs == 5 {
            led_products5(
                &om_v,
                f.shown(t_v.s_end)?,
                f.shown(t_v.s_end + 1)?,
                f.shown(t_v.s_end + 2)?,
                f.shown(t_v.s_end + 3)?,
            )
        } else {
            om_v[0] * f.shown(t_v.s_end)? * f.shown(t_v.s_end)?
                + om_v[1] * f.shown(t_v.s_end + 1)? * f.shown(t_v.s_end)?
                + om_v[2] * f.shown(t_v.s_end + 2)? * f.shown(t_v.s_end)?
        };
        t_v.row_u = psc_row(f, &mut t_v.p, s0, &Aff::default())?;
    }
    let cn = call_of_h(&l, "NF")?;
    let ch = call_of_h(&l, "HD0")?;
    let mut t_n = tsc_in(f, tr, &mut slot, zt_h(cn), lt as i32, 2, 2, calls)?;
    t_n.row_u = psc_row(
        f,
        &mut t_n.p,
        f.shown(t_n.s_end)? * f.shown(t_n.s_end + 1)?,
        &Aff::default(),
    )?;
    let mut t_h = tsc_rounds(f, tr, &mut slot, zt_h(ch), lt as i32, calls)?;
    let lam_s = hp.lam_s as usize;
    let mut st = super::lookup::HStack { lam: hp.lam_s, rs: vec![E::zero(); lam_s], p: Default::default() };
    for i in 0..lam_s {
        st.rs[lam_s - 1 - i] =
            round_in(f, tr, &mut slot, RoundForm::Eq2, &mut t_h.p, half, 0, calls)?;
    }
    t_h.s_end = psc_ends(f, tr, &mut slot, &mut t_h.p, 2, 2, calls)?;
    t_h.row_u = psc_row(
        f,
        &mut t_h.p,
        f.shown(t_h.s_end)? * f.shown(t_h.s_end + 1)?,
        &Aff::default(),
    )?;
    let s_v = t_h.s_end + 1;
    // The prover commits to U3, the evaluation tables.
    gate.root_in_h(f, tr, &[i_u3 as i32], calls)?;
    let zv = super::attention_shape::last_of(&wpl.r, la as usize)?;
    let yn = {
        let k = cut_last(zl_h(cn), cn.l_j as usize, ls as usize)?;
        super::attention_shape::long_point(k.lo, ls as usize, &t_n.r)
    };
    if yn.len() != la as usize || la != ls + lt {
        return Err(Refusal::named("plan-tensor-layout"));
    }
    let mut fun: Vec<HFun> = Vec::new();
    let mut p = 0u64;
    let mut tab: BTreeMap<String, u64> = BTreeMap::new();
    let mut tab_len: BTreeMap<u64, u64> = BTreeMap::new();
    let i_hf = 0usize;
    let i_hd = h.nhf as usize;
    let i_hr = i_hd + 1;
    let i_bh = i_hr + 1;
    let i_xl = i_bh + 1;
    let large = 1u64 << la;
    let mats = &hp.tl.mats;
    let mut add = |m0: usize, parts: u64, lf: u64, phi: &[E], nm: &str| -> Result<()> {
        tl.fun_open()?;
        let first = p;
        for q in 0..parts {
            let m = &mats[m0 + q as usize];
            fun.push(HFun {
                m: (m0 as u64 + q) as i32,
                l: lf,
                phi: phi.to_vec(),
                tree: 2,
                at: p,
                name: format!("{}{}{}", f.g, nm, if parts > 1 { format!(".{}", q) } else { String::new() }),
            });
            p += m.k * (m.m / lf);
        }
        if p == first {
            return Err(Refusal::internal(&format!("{}internal-h-table-index", f.g)));
        }
        tab.insert(String::from(nm), first);
        tab_len.insert(first, p - first);
        Ok(())
    };
    add(i_hf, h.nhf as u64, large, &super::attention_shape::long_phi(&zl, ls as usize, lt as usize), "hf@Z")?;
    let mut erc = E::zero();
    let mut phi_c = eq_tab(zt_h(ch), lt as usize);
    let mut rho_cv = vec![E::zero(); t as usize];
    for tq in 0..t as usize {
        if inp.on_c[tq] {
            erc = erc + phi_c[tq];
            rho_cv[tq] = E::one();
        } else {
            phi_c[tq] = E::zero();
        }
    }
    {
        let mut phi_z = vec![E::zero(); large as usize];
        for i in 0..large as usize {
            phi_z[i] = phi_c[i & (t as usize - 1)];
        }
        add(i_hf, h.nhf as u64, large, &phi_z, "hf@phiZ")?;
    }
    add(i_xl, 1, large, &super::attention_shape::long_phi(&zv, ls as usize, lt as usize), "xbL@Z_V")?;
    add(i_xl, 1, large, &super::attention_shape::long_phi(&yn, ls as usize, lt as usize), "xbL@Y_N")?;
    add(i_hd, 1, t, &eq_tab(zt_h(call_of_h(&l, "CNF")?), lt as usize), "hd@zt_FC")?;
    add(i_hd, 1, t, &eq_tab(&t_h.r, lt as usize), "hd@r_H")?;
    add(i_hr, 1, t, &eq_tab(zt_h(call_of_h(&l, "ROW")?), lt as usize), "hr@zt_ROW")?;
    add(i_hr, 1, t, &eq_tab(&pv, lt as usize), "hr@P_V")?;
    add(i_hr, 1, t, &eq_tab(&t_v.r, lt as usize), "hr@r_tV")?;
    add(i_hr, 1, t, &eq_tab(&t_n.r, lt as usize), "hr@rt_N")?;
    add(i_hr, 1, t, &phi_c, "hr@phiC")?;
    add(i_hr, 1, t, &rho_cv, "hr@rhoC")?;
    let mb = 1u64 << h.lmbh;
    add(i_bh, 1, mb, &forest_phi_b(&g1, h.lmbh as i32, 0)?, "bH-bits-0")?;
    add(i_bh, 1, mb, &forest_phi_b(&g1, h.lmbh as i32, 1)?, "bH-bits-1")?;
    add(i_bh, 1, mb, &forest_phi_p(h.lmbh as i32), "bH-pin")?;
    if p != hp.n_u[2] {
        return Err(Refusal::named("internal-W-length-H"));
    }
    tl.close_funs(&fun)?;
    tl.transcript(f, tr, &mut slot, &t2, gate, calls)?;
    // The weight claim on the output matrix Wh.
    let ew0 = ew_of(&l, "HD0")?;
    let wx0: E = {
        let mut s = E::zero();
        for v in 0..vv as usize {
            s = s + ew0[v];
        }
        s
    };
    let mut claims: Vec<WsClaim> = vec![WsClaim::default()];
    {
        let mut ui = inp.ws_lay.u.len();
        for (i, u) in inp.ws_lay.u.iter().enumerate() {
            if u.x == 13 {
                ui = i;
            }
        }
        if ui + 1 != inp.ws_lay.u.len() {
            return Err(Refusal::internal(&format!("{}internal-claim-unit", f.g)));
        }
        claims[0].ui = ui as u32;
        for gg in &inp.ws_lay.u[ui].g {
            let mut x = WsFac::default();
            if gg.name == "x" {
                let e_h = eq_tab(&t_h.r, lt as usize);
                let s_r = on_sum(inp, &t_h.r)?;
                x.av = vec![E::zero(); vv as usize];
                for v in 0..vv as usize {
                    x.av[v] = E::zero() - s_r * ew0[v];
                }
                for tq in 0..t as usize {
                    if !inp.on[tq] {
                        continue;
                    }
                    if inp.win[tq] >= vv as u32 {
                        return Err(Refusal::named("header-y"));
                    }
                    x.av[inp.win[tq] as usize] = x.av[inp.win[tq] as usize] + wx0 * e_h[tq];
                }
            } else if gg.name == "kk" {
                for i in 0..gg.z {
                    x.pt.push(st.rs[(gg.z - 1 - i) as usize]);
                }
                let e = eq_low(&st.rs, gg.z, st.lam);
                for hi in 0..gg.o {
                    x.hv.push(e[hi as usize]);
                }
            } else {
                return Err(Refusal::internal(&format!("{}internal-claim-factors", f.g)));
            }
            claims[0].f.push(x);
        }
    }
    if claims.len() as u64 != hp.n_cl {
        return Err(Refusal::internal(&format!("{}internal-claim-count", f.g)));
    }
    let mut wo = ws_fork_end(f, tr, &mut slot, inp.ws_lay, &claims, &[s_v], calls)?;
    if slot != hp.n_msg as u32 {
        return Err(Refusal::internal(&format!("{}internal-slot-count", f.g)));
    }
    f.plan_claims = hp.n_lin as u32;
    gate.batch(f, &mut t2, tr, slot, calls)?;
    // ---- The list of claims and the self-tests on it ----
    let s_ = |j: u32| Aff::slot(j);
    super::lookup::forest_objects(f, &g1)?;
    layer_object(f, &wpl)?;
    f.lin(&(s_(wpl.s_l) - s_(wpl.s_r)))?;
    {
        if y.xb.nl as i32 != limbs {
            return Err(Refusal::named("plan-tensor-layout"));
        }
        let e = super::attention_shape::hi_tab(&wpl.r, la as usize, (l_pd - ls as i32) as usize)?;
        let t = tab_at(&tab, "xbL@Z_V")?;
        let mut b = s_(wpl.s_l);
        for kh in 0..d / s2 {
            for l_ in 0..y.xb.nl as u64 {
                b = b + u3_at(f, i_u3, &tab_len, t, ten_cell(&y.xb, l_, 0, 0) / s2 + kh)?
                    * (E::zero() - e[kh as usize] * gp[l_ as usize]);
            }
        }
        f.lin(&b)?;
    }
    {
        let mut a = s_(t_v.s_cl);
        for i in 0..np_l {
            a = a + s_(s_pv + i as u32) * (E::zero() - om_v[i as usize]);
        }
        f.lin(&a)?;
        f.lin(&t_v.row_u)?;
    }
    if limbs == 5 {
        let r = row5_at_h(f, i_u3, &tab, &tab_len, "r_tV")?;
        f.lin(&(s_(t_v.s_end) - r.a.clone()))?;
        f.lin(&(s_(t_v.s_end + 1) - r.b.clone()))?;
        f.lin(&(s_(t_v.s_end + 2) - r.rlo.clone()))?;
        f.lin(&(s_(t_v.s_end + 3) - r.rhi.clone()))?;
        let q = row5_at_h(f, i_u3, &tab, &tab_len, "P_V")?;
        for s in 0..9usize {
            f.lin(&led_carry5(&q, s, &s_(s_w + s as u32)))?;
        }
        let mut pr = [Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default()];
        for j in 0..7u32 {
            pr[j as usize] = s_(s_pv + j);
        }
        let two = Aff::constant(ei(1i64 << (h.mf + 1)));
        let mut out = [Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default()];
        led_lines5(&q, &pr, ei(h.epsf as i64), &two, &mut out);
        for o in &out {
            f.lin(o)?;
        }
    } else {
        let r = row_at_h(f, i_u3, &tab, &tab_len, "r_tV")?;
        f.lin(&(s_(t_v.s_end) - r.sig.clone()))?;
        f.lin(&(s_(t_v.s_end + 1) - r.rlo.clone()))?;
        f.lin(&(s_(t_v.s_end + 2) - r.rhi.clone()))?;
        let q = row_at_h(f, i_u3, &tab, &tab_len, "P_V")?;
        for s in 0..7usize {
            f.lin(&(s_(s_w + s as u32) + q.c[s].clone() - q.dg[s].clone() - q.c[s + 1].clone() * ei(256)))?;
        }
        f.lin(&(q.v.clone() + Aff::constant(ei(h.epsf as i64)) - s_(s_pv) - q.l1.clone()))?;
        f.lin(&(q.l1.clone() + q.h1.clone() - q.sig.clone() * ei(2)))?;
        f.lin(&(s_(s_pv + 2) - q.p1.clone()))?;
        let n_f = Aff::constant(ei(1i64 << (h.mf + 1)));
        f.lin(&(n_f + q.sig.clone() - q.s0.clone() - s_(s_pv + 1) * ei(2) - q.p1.clone() * ei(1 << 25) - q.rr.clone() * ei(2)))?;
        f.lin(&(q.rr.clone() + q.rq.clone() - q.sig.clone() + Aff::constant(E::one())))?;
    }
    {
        let wh = ewh(&l, ls, s2, "NF")?;
        let t = tab_at(&tab, "xbL@Y_N")?;
        let mut sx = Aff::default();
        for kh in 0..d / s2 {
            sx = sx + xb_a_h(f, i_u3, &tab_len, t, y, s2, kh)? * wh[kh as usize];
        }
        f.lin(&t_n.row_u)?;
        let rr = if limbs == 5 { row5_at_h(f, i_u3, &tab, &tab_len, "rt_N")?.r } else { row_at_h(f, i_u3, &tab, &tab_len, "rt_N")?.r };
        f.lin(&(s_(t_n.s_end) - rr))?;
        f.lin(&(s_(t_n.s_end + 1) - sx))?;
    }
    let off_e = 128u64 * (((1u64 << (8 * EXC)) - 1) / 255) + 1;
    {
        let mut laid = vec![0u64; g1.nt as usize];
        let mut kf: Vec<Aff> = Vec::new();
        for q in 0..l.calls.len() {
            let c = &l.calls[q];
            let e = eq_tab(zl_h(c), c.l_j as usize);
            let mut weighed = vec![0u8; c.j as usize];
            let mut lines = Aff::default();
            for sg in &c.segs {
                lines = lines + line_form(f, &l, &tab, &tab_len, i_u3, h, y, ls, s2, lt, inp, &t_h, &t_n, erc, off_e, &sg.name)?;
                let entries = matches!(
                    sg.name.as_str(),
                    "HD0" | "HD1" | "HD2" | "HE0" | "HE1"
                );
                let v0 = if sg.name == "HE1" { hl.jva } else { 0 };
                for x in 0..sg.n {
                    let at = sg.pos[x as usize] as usize;
                    if weighed[at] != 0 {
                        return Err(Refusal::named("internal-h-join-place"));
                    }
                    weighed[at] = if entries && v0 + x >= vv { 2 } else { 1 };
                }
            }
            let mut pad_w = E::zero();
            for j in 0..c.j as usize {
                if weighed[j] == 0 {
                    pad_w = pad_w + e[j];
                }
                if weighed[j] != 1 {
                    laid[g1.first[q] as usize + (j >> (g1.d_t as usize - lt as usize))] += t;
                }
            }
            let mut v = Aff::constant(e_scale(pad_w, c.c.tau_at(c.c.t0)));
            if c.c.name == cn.c.name {
                v = v + s_(t_n.s_cl);
            }
            kf.push(v + lines);
        }
        super::lookup::forest_padding_laid(&g1, &laid)?;
        let join = forest_join(&g1, &kf)?;
        f.lin(&join)?;
    }
    // The four lines on the hidden numbers (the acceptance policy).
    {
        let r_ = ei(inp.hrc as i64);
        let g0 = gap_at(f, i_u3, &tab, &tab_len, limbs, "rhoC", 0, r_)?;
        let g1 = gap_at(f, i_u3, &tab, &tab_len, limbs, "rhoC", 1, r_)?;
        let g2 = gap_at(f, i_u3, &tab, &tab_len, limbs, "rhoC", 2, r_)?;
        let g4 = gap_at(f, i_u3, &tab, &tab_len, limbs, "rhoC", 4, r_)?;
        f.lin(&(g0 + g1.clone() * ei(h.clipc as i64) + g2
            - Aff::constant(e_scale(r_, h.theta as u64))))?;
        f.lin(&(g1 + g4 - Aff::constant(ei(if inp.hrc != 0 { h.cap as i64 } else { 0 }))))?;
        let p0 = gap_at(f, i_u3, &tab, &tab_len, limbs, "phiC", 0, erc)?;
        let p3 = gap_at(f, i_u3, &tab, &tab_len, limbs, "phiC", 3, erc)?;
        f.lin(&(p0 + p3 - Aff::constant(e_scale(erc, h.clipc as u64))))?;
        let te = tab_at(&tab, "hf@phiZ")?;
        let mut a = gap_at(f, i_u3, &tab, &tab_len, limbs, "phiC", 5, erc)?;
        a = a + Aff::constant(e_scale(erc, off_e) * ei(hl.jv as i64) - e_scale(erc, (hl.jv - vv + 1) << h.famf));
        let mut sc = 1u64;
        for l_ in 0..EXC as u64 {
            for xh in 0..hl.jv / s2 {
                a = a + u3_at(f, i_u3, &tab_len, te, (hl.oe + l_ * hl.jv) / s2 + xh)? * ei(sc as i64);
            }
            sc *= 256;
        }
        f.lin(&a)?;
    }
    // The forest's three claims on the bits of its multiplicities.
    {
        let t_b = [tab_at(&tab, "bH-bits-0")?, tab_at(&tab, "bH-bits-1")?];
        let t_p = tab_at(&tab, "bH-pin")?;
        let w = (g1.k_t + 5 - h.lmbh as i32) as u32;
        let cols = (g1.nc as u64) << w;
        let mut tb_vals: [Vec<Aff>; 2] = [Vec::new(), Vec::new()];
        for e in 0..2usize {
            for col in 0..cols {
                if col >= hl.kb {
                    return Err(Refusal::internal(&format!("{}internal-h-table-index", f.g)));
                }
                tb_vals[e].push(u3_at(f, i_u3, &tab_len, t_b[e], col)?);
            }
        }
        let mut tp_vals: Vec<Aff> = Vec::new();
        for col in 0..cols {
            if col >= hl.kb {
                return Err(Refusal::internal(&format!("{}internal-h-table-index", f.g)));
            }
            tp_vals.push(u3_at(f, i_u3, &tab_len, t_p, col)?);
        }
        forest_plane_lins(f, &mut g1, h.lmbh as i32, |e, x| tb_vals[e as usize][x as usize].clone(), |x| tp_vals[x as usize].clone())?;
    }
    tl.objects(f, &fun)?;
    {
        let eq = eq_low(&st.rs, 0, st.lam);
        let t = tab_at(&tab, "hd@r_H")?;
        let mut alin = Aff::default();
        for kk in 0..d {
            alin = alin + sh2(f, i_u3, &tab_len, t, d, kk)? * eq[kk as usize];
        }
        f.lin(&t_h.row_u)?;
        f.lin(&(s_(t_h.s_end) - alin))?;
    }
    ws_fork_lin(f, &mut wo.merged)?;
    for j in 0..hp.n_msg as u32 {
        if (f.ls[j as usize] == E::zero()) != (j == wo.merged.s_fv) {
            return Err(Refusal::internal(&format!("{}internal-h-free-slot", f.g)));
        }
    }
    if f.n_claim != hp.n_lin as u32 {
        return Err(Refusal::internal(&format!("{}internal-h-claim-count", f.g)));
    }
    if tl.fold_drawn != 1 {
        return Err(Refusal::internal(&format!("{}internal-h-rows-booked", f.g)));
    }
    if 1 + tl.groups_run() != 2 {
        return Err(Refusal::internal(&format!("{}internal-h-calls-booked", f.g)));
    }
    tl.funs_held(f, &fun)?;
    tl.self_test(f, hp.n_u)?;
    tl.coefficients(f)?;
    tl.tile_self_test(f, &t2)?;
    let eq_laid = tl.equations_laid()?;
    gate.door_h(f, &mut t2, tr, eq_laid, calls)?;
    if f.n_claim != f.plan_claims {
        return Err(Refusal::internal(&format!("{}internal-f-draws", f.g)));
    }
    f.kap_all_taken()?;
    tl.fold_all_taken(f)?;
    Ok(HeadRunOut { wo, nc, nm: tl.nm, n_claim: f.n_claim, n_slots: f.ns })
}

/// `onSum(P)`: the sum of eq(P, t) over the covered positions.
fn on_sum(inp: &HeadCheckInputs<'_>, p: &[E]) -> Result<E> {
    let e = eq_tab(p, inp.h.lt as usize);
    let mut s = E::zero();
    for tq in 0..inp.y.t as usize {
        if inp.on[tq] {
            s = s + e[tq];
        }
    }
    Ok(s)
}

/// One digit row (four limbs) of the head's norm (`rowAt` with table `hr@P`).
#[derive(Clone)]
struct RowH {
    dg: [Aff; 74],
    v: Aff,
    c: [Aff; 8],
    s0: Aff,
    sig: Aff,
    l1: Aff,
    h1: Aff,
    rlo: Aff,
    rhi: Aff,
    r: Aff,
    p1: Aff,
    rr: Aff,
    rq: Aff,
}

impl Default for RowH {
    fn default() -> Self {
        RowH {
            dg: core::array::from_fn(|_| Aff::default()),
            v: Aff::default(),
            c: core::array::from_fn(|_| Aff::default()),
            s0: Aff::default(),
            sig: Aff::default(),
            l1: Aff::default(),
            h1: Aff::default(),
            rlo: Aff::default(),
            rhi: Aff::default(),
            r: Aff::default(),
            p1: Aff::default(),
            rr: Aff::default(),
            rq: Aff::default(),
        }
    }
}

fn row_at_h(
    f: &HFork,
    i_u3: u32,
    tab: &BTreeMap<String, u64>,
    tab_len: &BTreeMap<u64, u64>,
    p: &str,
) -> Result<RowH> {
    let t = tab_at(tab, &format!("hr@{}", p))?;
    let mut r = RowH::default();
    for j in 0..74u64 {
        r.dg[j as usize] = u3_at(f, i_u3, tab_len, t, j)? + Aff::constant(ei(128));
    }
    let dig = |r: &RowH, a: usize, n: usize| -> Aff {
        let mut s = Aff::default();
        let mut sc = 1u64;
        for j in 0..n {
            s = s + r.dg[a + j].clone() * ei(sc as i64);
            sc *= 256;
        }
        s
    };
    r.v = dig(&r, 0, 8);
    for s in 1..=6usize {
        r.c[s] = dig(&r, 8 + 6 * (s - 1), 6) - Aff::constant(ei(1i64 << 47));
    }
    r.c[7] = r.dg[7].clone();
    r.s0 = r.dg[45].clone();
    r.sig = r.dg[44].clone() * ei(2)
        + r.dg[45].clone()
        + r.dg[46].clone() * ei(256)
        + r.dg[47].clone() * ei(65536)
        + r.dg[48].clone() * ei(1 << 24);
    r.l1 = dig(&r, 49, 4);
    r.h1 = dig(&r, 53, 4);
    r.rlo = dig(&r, 57, 3);
    r.rhi = dig(&r, 60, 3);
    r.r = r.rlo.clone() + r.rhi.clone() * ei(1 << 24);
    r.p1 = dig(&r, 63, 3);
    r.rr = dig(&r, 66, 4);
    r.rq = dig(&r, 70, 4);
    Ok(r)
}

fn row5_at_h(
    f: &HFork,
    i_u3: u32,
    tab: &BTreeMap<String, u64>,
    tab_len: &BTreeMap<u64, u64>,
    p: &str,
) -> Result<Row5<Aff>> {
    let t = tab_at(tab, &format!("hr@{}", p))?;
    let mut cells: Vec<Aff> = Vec::with_capacity(99);
    for j in 0..99u64 {
        cells.push(u3_at(f, i_u3, tab_len, t, j)?);
    }
    Ok(row5(|j| cells[j].clone()))
}

/// `sh2(t, j)`: two limbs of a table at radix 256.
fn sh2(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    t: u64,
    d: u64,
    j: u64,
) -> Result<Aff> {
    Ok(u3_at(f, i_u3, tab_len, t, j)? + u3_at(f, i_u3, tab_len, t, d + j)? * ei(256))
}

/// `xbA(t, kh)` in the head's tables.
#[allow(clippy::too_many_arguments)]
fn xb_a_h(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    t: u64,
    y: &Lay,
    s2: u64,
    kh: u64,
) -> Result<Aff> {
    let mut s = Aff::default();
    let mut sc = 1u64;
    for l in 0..y.xb.nl as u64 {
        s = s + u3_at(f, i_u3, tab_len, t, ten_cell(&y.xb, l, 0, 0) / s2 + kh)? * ei(sc as i64);
        sc *= 256;
    }
    Ok(s)
}

/// `gapAt(P, i, wsum)`.
#[allow(clippy::too_many_arguments)]
fn gap_at(
    f: &HFork,
    i_u3: u32,
    tab: &BTreeMap<String, u64>,
    tab_len: &BTreeMap<u64, u64>,
    limbs: i32,
    p: &str,
    i: usize,
    wsum: E,
) -> Result<Aff> {
    let t = tab_at(tab, &format!("hr@{}", p))?;
    let o = led_nr(limbs) as u64 + LEDG[i].0;
    let mut s = Aff::default();
    let mut sc = 1u64;
    for l in 0..LEDG[i].1 {
        s = s + (u3_at(f, i_u3, tab_len, t, o + l as u64)? + Aff::constant(e_scale(wsum, 128)))
            * ei(sc as i64);
        sc *= 256;
    }
    Ok(s)
}

/// `wxOf`: the sum of a segment's column coefficients over `v < Vv`.
fn wx_of(ew: &[E], vv: u64) -> E {
    let mut s = E::zero();
    for v in 0..vv as usize {
        s = s + ew[v];
    }
    s
}

/// `placeTermH`: `[v < win_t]`, summed over the real places.
fn place_term(inp: &HeadCheckInputs<'_>, ew: &[E], et: &[E]) -> E {
    let vv = inp.h.v as usize;
    let mut pre = vec![E::zero(); vv];
    for v in 1..vv {
        pre[v] = pre[v - 1] + ew[v - 1];
    }
    let mut s = E::zero();
    for t in 0..inp.y.t as usize {
        if inp.on[t] {
            s = s + et[t] * pre[inp.win[t] as usize];
        }
    }
    s
}

/// `LINE(sn)` of the head's check (vf_output_head_check.inc:461-515).
#[allow(clippy::too_many_arguments)]
fn line_form(
    f: &HFork,
    hl: &super::stage_context::Hl,
    tab: &BTreeMap<String, u64>,
    tab_len: &BTreeMap<u64, u64>,
    i_u3: u32,
    h: &Hdr,
    y: &Lay,
    ls: u32,
    s2: u64,
    lt: u32,
    inp: &HeadCheckInputs<'_>,
    t_h: &TokenSumcheckState,
    _t_n: &TokenSumcheckState,
    erc: E,
    off_e: u64,
    sn: &str,
) -> Result<Aff> {
    let ew = ew_of(hl, sn)?;
    let w = sum_e(&ew);
    let o1 = ei(128);
    let o2 = ei(32896);
    let s_ = |j: u32| Aff::slot(j);
    let sl = |sn: &str, off: u64, nl: usize, j: u64| -> Result<Aff> {
        let wh = ewh(hl, ls, s2, sn)?;
        let t = tab_at(tab, "hf@Z")?;
        let mut s = Aff::default();
        for xh in 0..wh.len() as u64 {
            let mut sc = 1u64;
            for l in 0..nl {
                s = s + u3_at(f, i_u3, tab_len, t, (off + l as u64 * j) / s2 + xh)?
                    * e_scale(wh[xh as usize], sc);
                sc *= 256;
            }
        }
        Ok(s)
    };
    let zt_of = |sn: &str| -> Result<&[E]> {
        let c = call_of_h(hl, sn)?;
        Ok(zt_h(c))
    };
    match sn {
        "NF" => Ok(Aff::constant(w * (pw(h.kf - 1) - pw(16) * o2))
            - sl(sn, hl.oaw, 2, h.d)? * pw(h.kf)
            - sl(sn, hl.ora, 2, h.d)? * pw(16)),
        "NFH" => Ok((Aff::constant(o2 * w) + sl(sn, hl.ora, 2, h.d)?) * pw(32 - h.kf)),
        "HD0" | "HD1" | "HD2" => {
            let wx = wx_of(&ew, inp.h.v);
            let w_r = wx * on_sum(inp, zt_of(sn)?)?;
            if sn == "HD1" {
                return Ok(Aff::constant(o2 * w_r) + sl(sn, hl.od1, 2, hl.jv)?);
            }
            if sn == "HD2" {
                return Ok(Aff::constant(o1 * w_r) + sl(sn, hl.od2, 1, hl.jv)?);
            }
            let et = eq_tab(zt_of("HD0")?, lt as usize);
            let iw = pw(h.digsh + 15).inv();
            Ok((s_(t_h.s_cl) * pw(y.l_pd as u32)
                + (gap_at(f, i_u3, tab, tab_len, inp.limbs, "phiC", 0, erc)?
                    + gap_at(f, i_u3, tab, tab_len, inp.limbs, "phiC", 1, erc)? * eb(BIGH))
                    * wx
                - Aff::constant(place_term(inp, &ew, &et))
                - (Aff::constant(o2 * w_r) + sl(sn, hl.od1, 2, hl.jv)?) * pw(h.digsh)
                - (Aff::constant(o1 * w_r) + sl(sn, hl.od2, 1, hl.jv)?))
                * iw)
        }
        "HE0" | "HE1" => {
            let v0 = if sn == "HE1" { hl.jva } else { 0 };
            let mut wx = E::zero();
            for x in 0..ew.len() as u64 {
                if v0 + x < inp.h.v {
                    wx = wx + ew[x as usize];
                }
            }
            Ok(Aff::constant(o2 * wx * on_sum(inp, zt_of(sn)?)?)
                + sl(sn, hl.od1 + v0, 2, hl.jv)?
                + (Aff::constant(e_scale(w, off_e)) + sl(sn, hl.oe + v0, EXC, hl.jv)?) * pw(16))
        }
        "ROW" => {
            let t = tab_at(tab, "hr@zt_ROW")?;
            let mut a = Aff::default();
            for idx in 0..led_nrh(inp.limbs) {
                let mu = if idx < led_nr(inp.limbs) {
                    led_mu(idx, inp.limbs)
                } else {
                    1
                };
                a = a
                    + (u3_at(f, i_u3, tab_len, t, idx as u64)? + Aff::constant(ei(128)))
                        * e_scale(ew[idx as usize], mu);
            }
            Ok(a)
        }
        "CNF" => {
            let t = tab_at(tab, "hd@zt_FC")?;
            let mut b = Aff::default();
            for x in 0..h.d {
                b = b + sh2(f, i_u3, tab_len, t, h.d, x)? * ew[x as usize];
            }
            Ok(sl(sn, hl.oaw, 2, h.d)?
                + b * pw(28)
                + Aff::constant(w * ei((1i64 << 15) + (1i64 << 39))))
        }
        _ => Err(Refusal::named(&format!("internal-line-{}", sn))),
    }
}

fn eb(v: u64) -> E {
    E::from_base(crate::field::ext::F::from_u64(v))
}
