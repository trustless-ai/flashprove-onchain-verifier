//! The attention sub-proof's check, ported from `AttentionSubProof::run()` in
//! `verifier/src/vf_attention_check.h`.
//!
//! `run()` reads A_g's messages from the request's first chain through a [`Tr`], adds the linear
//! claims and passes their one equation to the segment gate. It tests none of them; the chain
//! tests the equation at its end. To reject, it returns a [`Refusal`]; a name with `internal-`
//! marks a self-check of this program.
//!
//! C++ takes the channel from `currentSegment->V->ch`; here the caller passes the [`Tr`] it has
//! already bound to that chain, and the segment calls that C++ reaches through `currentSegment`
//! go through [`AttentionSegment`].

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::refusal::{Refusal, Result};

use super::attention_check::{AttentionSegment, AttentionSubProof};
use super::attention_shape::{
    eq_at, eq_pts, head_feat, id_of, le_of, ones_of, ten_cell, ACall, TenAt, S_FD, S_FM, S_IX,
    S_RD, S_RM, S_WH, S_WL,
};
use super::common::eq_tab;
use super::engine::{Aff, HFork};
use super::lookup::{
    forest_join, forest_objects, forest_pad, forest_padding_laid, forest_phi_b, forest_phi_p,
    forest_planes_added, forest_pub_run, u_ent, HFun,
};
use super::packing::e_scale;
use super::sumcheck::{
    psc_row, sc3_a, sc3_b, sc3_in, sc3_row, scd_in, Degree3SumcheckState,
};
use super::transcript::{tr_batch, tr_point, RoundName, Tr};

// The C++ helpers that the run uses, without the C++ header's free functions.
use super::attention_shape::{block_rows, cut_last};

fn eb(v: u64) -> E {
    E::from_base(crate::field::ext::F::from_u64(v))
}

fn ei(v: i64) -> E {
    E::from_base(crate::field::ext::F::from_u64(super::common::fint(v)))
}

fn s_aff(s: u32) -> Aff {
    Aff::slot(s)
}

fn u3_at(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    t: u64,
    i: u64,
) -> Result<Aff> {
    let len = match tab_len.get(&t) {
        Some(&len) => len,
        None => return Err(Refusal::internal(&format!("{}internal-a-table-index", f.g))),
    };
    if i >= len {
        return Err(Refusal::internal(&format!("{}internal-a-table-index", f.g)));
    }
    u_ent(f, i_u3, t + i)
}

#[allow(clippy::too_many_arguments)]
fn plane(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    t: u64,
    x: i32,
    lam: u64,
    a: u64,
    z: &[E],
    is_d: bool,
    n_m: i32,
    n_d: i32,
    lm_s: i32,
    lam_count: u64,
    ha: u64,
) -> Result<Aff> {
    let nb = if is_d { n_d } else { n_m } as u64;
    let a0 = (if is_d { 5 * lam_count * ha << n_m } else { 0 })
        + ((((x as u64) * lam_count + lam) * ha + a) << nb);
    let eh = eq_tab(z, (nb - lm_s as u64) as usize);
    let mut s = Aff::default();
    for (hi, &e) in eh.iter().enumerate() {
        s.add(&u3_at(f, i_u3, tab_len, t, (a0 >> lm_s) + hi as u64)?, e);
    }
    Ok(s)
}

/// `shV(t, OFF, nl, J, lam, j)`: entry `OFF + ((l * Lam + lam) * J + j)` for `l < nl`, with `Lam`
/// the shape's (C++ captures it from `run()`; the argument `lam` is the piece's).
fn sh_v(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    t: u64,
    off: u64,
    nl: u32,
    j: u64,
    lam: u64,
    jj: u64,
    lam_shape: u64,
) -> Result<Aff> {
    let mut s = Aff::default();
    let mut sc = 1u64;
    for l in 0..nl {
        s.add(
            &u3_at(f, i_u3, tab_len, t, off + ((l as u64) * lam_shape + lam) * j + jj)?,
            ei(sc as i64),
        );
        sc *= 256;
    }
    Ok(s)
}

#[allow(clippy::too_many_arguments)]
fn xl(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    t: u64,
    x: &TenAt,
    lam: u64,
    hd: u64,
    zc: &[E],
    dh: u64,
    ls: i32,
    s2: u64,
) -> Result<Aff> {
    let k = cut_last(zc, zc.len(), ls as usize)?;
    let ec = eq_tab(k.hi, k.nhi);
    let j0 = head_feat(x, hd, dh)?;
    let mut s = Aff::default();
    for (ch, &e) in ec.iter().enumerate() {
        let mut sc = 1u64;
        for l in 0..x.nl {
            s.add(
                &u3_at(
                    f,
                    i_u3,
                    tab_len,
                    t,
                    ten_cell(x, l, lam, j0) / s2 + ch as u64,
                )?,
                e_scale(e, sc),
            );
            sc *= 256;
        }
    }
    Ok(s)
}

fn over_g<FN>(zg: &[E], lgk: usize, g_count: u64, mut g: FN) -> Result<Aff>
where
    FN: FnMut(u64) -> Result<Aff>,
{
    let eg = eq_tab(zg, lgk);
    let mut s = Aff::default();
    for gg in 0..g_count {
        s.add(&g(gg)?, eg[gg as usize]);
    }
    Ok(s)
}

impl AttentionSubProof {
    /// `AttentionSubProof::run()`.
    pub fn run(
        &mut self,
        g_: &str,
        tr: &mut Tr<'_, '_, '_, '_>,
        gate: &mut dyn AttentionSegment,
        calls_hc: &mut HashCalls,
    ) -> Result<()> {
        let cf = self.a.cf.clone();
        let (lt, lgk, ldh, lm_s, ln_t, ls, n_m, n_d) =
            (cf.lt, cf.lgk, cf.ldh, cf.lm_s, self.a.ln_t, self.a.ls, self.a.n_m, self.a.n_d);
        let (h, t, _b, n_t, h_p, g, ha, dh, dq, lam) =
            (cf.h, self.a.t, self.a.b, self.a.n_t, self.a.h_p, self.a.g, self.a.ha, self.a.dh, self.a.dq, self.a.lam);
        let _ = h_p;
        self.a.bind_tau();
        let mut f = HFork::default();
        f.g = String::from(g_);
        self.seam.start(&mut f, self.ns);
        let mut slot = 0u32;
        // Step 1: the lookup's messages, for all calls as one group.
        let calls_in: Vec<super::common::Call> = self.a.calls.iter().map(|c| c.c.clone()).collect();
        let mut g1 = forest_pad(
            &mut f,
            tr,
            &calls_in,
            &self.fs.pub_,
            &mut slot,
            self.input.lidb,
            calls_hc,
        )?;
        for q in 0..self.a.calls.len() {
            self.a.calls[q].c.alpha = g1.alpha;
            self.a.calls[q].c.zk = g1.zk[q].clone();
        }
        let mut weighed: Vec<Vec<bool>> = self
            .a
            .calls
            .iter()
            .map(|c| vec![false; c.pcs.len()])
            .collect();
        // Pairs (lam, a) and their piece weight.
        #[derive(Clone)]
        struct PW {
            lam: u64,
            a: u64,
            wp: E,
        }
        fn pieces(c: &ACall, seg: i32, weighed: &mut [bool]) -> Vec<PW> {
            let mut v = Vec::new();
            for (i, pc) in c.pcs.iter().enumerate() {
                if pc.seg == seg {
                    weighed[i] = true;
                    v.push(PW {
                        lam: pc.lam,
                        a: pc.a,
                        wp: eq_at(&c.c.zk, (c.c.n - pc.b) as usize, pc.off >> pc.b),
                    });
                }
            }
            v.sort_by(|x, y| if x.lam != y.lam { x.lam.cmp(&y.lam) } else { x.a.cmp(&y.a) });
            v
        }
        let inner = |c: &ACall, seg: i32| -> Vec<E> {
            let b = seg_len(c, seg);
            c.c.zk[c.c.zk.len() - b as usize..].to_vec()
        };
        let sum_w = |v: &[PW]| -> E {
            let mut s = E::zero();
            for x in v {
                s = s + x.wp;
            }
            s
        };
        #[allow(dead_code)]
        struct PlaneClaim {
            call: usize,
            seg: i32,
            z: Vec<E>,
            is_d: bool,
            pw: Vec<PW>,
            s0: u32,
            np: i32,
        }
        // Step 3.
        let mut pcl: Vec<PlaneClaim> = Vec::new();
        for q in 0..self.nc {
            if self.a.calls[q].kind == "KR" {
                for seg in [S_RM, S_RD] {
                    if !Self::holds(&self.a.calls[q], seg) {
                        continue;
                    }
                    let z = inner(&self.a.calls[q], seg);
                    let pw = pieces(&self.a.calls[q], seg, &mut weighed[q]);
                    let s0 = f.claims_in(tr, &mut slot, (3) as u32)?;
                    pcl.push(PlaneClaim { call: q, seg, z, is_d: seg == S_RD, pw, s0, np: 3 });
                }
            }
        }
        // Step 4.
        #[allow(dead_code)]
        struct KF {
            call: usize,
            claim: usize,
            seg: i32,
            pw: Vec<PW>,
            zg: Vec<E>,
            z_p: Vec<E>,
            z_s: Vec<E>,
            z_i: Vec<E>,
            zi: Vec<E>,
            zj: Vec<E>,
            wi: Vec<E>,
            w: Vec<E>,
            s0: u32,
            sc: Degree3SumcheckState,
            t_m: u64,
            t_q: u64,
            t_k: u64,
        }
        let mut kfs: Vec<KF> = Vec::new();
        for q in 0..self.nc {
            if self.a.calls[q].kind != "KFD" {
                continue;
            }
            for seg in [S_FM, S_FD] {
                if !Self::holds(&self.a.calls[q], seg) {
                    continue;
                }
                let pw = pieces(&self.a.calls[q], seg, &mut weighed[q]);
                let z = inner(&self.a.calls[q], seg);
                let mut at = 0usize;
                let zg = z[at..at + lgk as usize].to_vec();
                at += lgk as usize;
                let mut z_p = Vec::new();
                let mut z_s = Vec::new();
                let mut z_i = Vec::new();
                if seg == S_FM {
                    z_p = z[at..at + ln_t as usize - 1].to_vec();
                    at += ln_t as usize - 1;
                    z_s = z[at..at + ln_t as usize].to_vec();
                    at += ln_t as usize;
                } else {
                    z_i = z[at..at + ln_t as usize].to_vec();
                    at += ln_t as usize;
                }
                let zi = z[at..at + cf.l_b as usize].to_vec();
                at += cf.l_b as usize;
                let zj = z[at..at + cf.l_b as usize].to_vec();
                let s0 = f.claims_in(tr, &mut slot, (7) as u32)?;
                let claim = pcl.len();
                pcl.push(PlaneClaim { call: q, seg, z: z.clone(), is_d: seg == S_FD, pw: pw.clone(), s0, np: 5 });
                let mut wi = vec![E::zero(); n_t as usize];
                if seg == S_FM {
                    let e_p = eq_tab(&z_p, ln_t as usize - 1);
                    let es = eq_tab(&z_s, ln_t as usize);
                    for p in 0..h_p {
                        for sg in 0..n_t - 1 {
                            let (ii, _jj) = self.a.cover(p, sg);
                            wi[ii as usize] = wi[ii as usize] + e_p[p as usize] * es[sg as usize];
                        }
                    }
                } else {
                    wi = eq_tab(&z_i, ln_t as usize);
                }
                let mut sc = sc3_in(
                    &mut f,
                    tr,
                    &mut slot,
                    self.nv_kf(seg),
                    pw.len(),
                    &Aff::slot(s0 + 6),
                    calls_hc,
                )?;
                let mut w = vec![E::zero(); pw.len()];
                {
                    let r = sc.r.clone();
                    let mut ff = eq_pts(&zg, &r, lgk as usize);
                    if seg == S_FM {
                        ff = ff
                            * eq_pts(&z_p, &r[lgk as usize..], ln_t as usize - 1)
                            * (eq_pts(&z_s, &r[lgk as usize + ln_t as usize - 1..], ln_t as usize)
                                - ones_of(&z_s, ln_t as usize)
                                    * ones_of(&r[lgk as usize + ln_t as usize - 1..], ln_t as usize));
                    } else {
                        ff = ff * eq_pts(&z_i, &r[lgk as usize..], ln_t as usize);
                    }
                    for (bi, p) in pw.iter().enumerate() {
                        w[bi] = p.wp * ff;
                    }
                }
                sc3_row(&mut f, &mut sc, &w, &self.a.calls[q].c.name)?;
                kfs.push(KF {
                    call: q,
                    claim,
                    seg,
                    pw,
                    zg,
                    z_p,
                    z_s,
                    z_i,
                    zi,
                    zj,
                    wi,
                    w,
                    s0,
                    sc,
                    t_m: 0,
                    t_q: 0,
                    t_k: 0,
                });
            }
        }
        // Step 5.
        let mut c_wl: Option<usize> = None;
        let mut c_ix: Option<usize> = None;
        let mut c_w: Option<usize> = None;
        for (q, c) in self.a.calls.iter().enumerate() {
            if Self::holds(c, S_WL) {
                c_wl = Some(q);
            }
            if Self::holds(c, S_IX) {
                c_ix = Some(q);
            }
            if Self::holds(c, S_WH) {
                c_w = Some(q);
            }
        }
        let (qwl, qix, qw) = match (c_wl, c_ix, c_w) {
            (Some(a), Some(b), Some(c)) => (a, b, c),
            _ => return Err(Refusal::named("internal-af-calls")),
        };
        let pw_w = pieces(&self.a.calls[qwl], S_WL, &mut weighed[qwl]);
        let pw_x = pieces(&self.a.calls[qix], S_IX, &mut weighed[qix]);
        let pw_h = pieces(&self.a.calls[qw], S_WH, &mut weighed[qw]);
        if pw_w.len() != self.np || pw_x.len() != self.np || pw_h.len() != self.np {
            return Err(Refusal::named("internal-af-calls"));
        }
        let zw = inner(&self.a.calls[qwl], S_WL);
        let zx = inner(&self.a.calls[qix], S_IX);
        let zh = inner(&self.a.calls[qw], S_WH);
        let zsl = zw[0];
        let zg_w = &zw[1..];
        let zi_w = &zg_w[lgk as usize..];
        let zc_w = &zi_w[lt as usize..];
        let zg_x = &zx[..];
        let zi_x = &zg_x[lgk as usize..];
        let zg_h = &zh[..];
        let zi_h = &zg_h[lgk as usize..];
        let zc_h = &zi_h[lt as usize..];
        let s5 = f.claims_in(tr, &mut slot, (5) as u32)?;
        let s_ib = f.claims_in(tr, &mut slot, (lt as usize) as u32)?;
        let s5h = f.claims_in(tr, &mut slot, (2) as u32)?;
        let s_acc = s5;
        let s_zo = s5 + 1;
        let s_zc = s5 + 2;
        let s_rh = s5 + 3;
        let s_rhp = s5 + 4;
        let lww = sum_w(&pw_w);
        let lwx = sum_w(&pw_x);
        let lwh = sum_w(&pw_h);
        let times_w = |pw: &[PW], ff: E| -> Vec<E> {
            pw.iter().map(|x| x.wp * ff).collect()
        };
        let mut sc_e = sc3_in(
            &mut f,
            tr,
            &mut slot,
            self.nv_e(),
            self.np,
            &Aff::slot(s_zo),
            calls_hc,
        )?;
        let f_e = eq_pts(zg_w, &sc_e.r, lgk as usize) * eq_pts(zi_w, &sc_e.r[lgk as usize..], lt as usize);
        sc3_row(&mut f, &mut sc_e, &times_w(&pw_w, f_e), "e")?;
        // Step 6.
        let gam_p = tr_batch(tr, 2, calls_hc)?;
        let zi_hi = &zi_w[..ln_t as usize];
        let zi_lo = &zi_w[ln_t as usize..];
        let s_cl = f.claims_in(tr, &mut slot, (2) as u32)?;
        let mut vpm = sc3_in(
            &mut f,
            tr,
            &mut slot,
            self.nv_vm(),
            self.np,
            &Aff::slot(s_cl),
            calls_hc,
        )?;
        let mut wjv = vec![E::zero(); n_t as usize];
        {
            let r = vpm.r.clone();
            let e_ih = eq_tab(zi_hi, ln_t as usize);
            let e_p = eq_tab(&r[lgk as usize..], ln_t as usize - 1);
            let es = eq_tab(&r[lgk as usize + ln_t as usize - 1..], ln_t as usize);
            let mut ff = E::zero();
            for p in 0..h_p {
                for sg in 0..n_t - 1 {
                    let (ii, jj) = self.a.cover(p, sg);
                    ff = ff + e_p[p as usize] * es[sg as usize] * e_ih[ii as usize];
                    wjv[jj as usize] = wjv[jj as usize] + e_p[p as usize] * es[sg as usize];
                }
            }
            sc3_row(
                &mut f,
                &mut vpm,
                &times_w(&pw_w, ff * eq_pts(zg_w, &r, lgk as usize)),
                "VPM",
            )?;
        }
        let mut vpd = sc3_in(
            &mut f,
            tr,
            &mut slot,
            self.nv_vd(),
            self.np,
            &Aff::slot(s_cl + 1),
            calls_hc,
        )?;
        let f_vpd = eq_pts(zg_w, &vpd.r, lgk as usize) * eq_pts(zi_hi, &vpd.r[lgk as usize..], ln_t as usize);
        sc3_row(&mut f, &mut vpd, &times_w(&pw_w, f_vpd), "VPD")?;
        // Step 7.
        let points = tr_point(
            tr,
            RoundName::Zero,
            (2 * lgk + 2 * lt + 4) as usize,
            calls_hc,
        )?;
        let part = |first: usize, n: usize| -> Vec<E> { points[first..first + n].to_vec() };
        let tg = part(0, lgk as usize);
        let ti = part(lgk as usize, lt as usize);
        let tk = part((lgk + lt) as usize, 4);
        let tbg = part((lgk + lt + 4) as usize, lgk as usize);
        let tbi = part((2 * lgk + lt + 4) as usize, lt as usize);
        let s_m6 = f.claims_in(tr, &mut slot, (self.np) as u32)?;
        let om = tr_batch(tr, self.np, calls_hc)?;
        let mut start_f = Aff::default();
        for b in 0..self.np {
            start_f.add(&Aff::slot(s_m6 + b as u32), om[b]);
        }
        let mut sc_f = sc3_in(
            &mut f,
            tr,
            &mut slot,
            self.nv_f(),
            self.np,
            &start_f,
            calls_hc,
        )?;
        {
            let ri = &sc_f.r[..lt as usize];
            let rg = &sc_f.r[lt as usize..lt as usize + lgk as usize];
            let f_f = eq_pts(&tg, rg, lgk as usize) * eq_pts(&ti, ri, lt as usize);
            let wf: Vec<E> = (0..self.np).map(|b| om[b] * f_f).collect();
            sc3_row(&mut f, &mut sc_f, &wf, "f")?;
        }
        let om4 = tr_batch(tr, self.np, calls_hc)?;
        let mut start_d = Aff::default();
        for b in 0..self.np {
            start_d.add(&sc3_b(&sc_f, b), om4[b]);
        }
        let mut scd = scd_in(
            &mut f,
            tr,
            &mut slot,
            &self.scd_degrees(),
            lt + 1,
            lam as usize + self.np * lt as usize,
            &start_d,
            calls_hc,
        )?;
        let pj = &scd.r[..lt as usize];
        let pg = &scd.r[lt as usize..lt as usize + lgk as usize];
        let pi = &scd.r[lt as usize + lgk as usize..];
        let s_kc = scd.s_end;
        let s_ib_at = |b: usize, k: i32| -> u32 { s_kc + (lam as usize + b * lt as usize + k as usize) as u32 };
        {
            let mut s0 = E::zero();
            for b in 0..self.np {
                let mut tt = om4[b] * f.shown(s_kc + (b / ha as usize) as u32)?;
                for k in 0..lt {
                    let y = pj[(lt - 1 - k) as usize];
                    tt = tt
                        * (f.shown(s_ib_at(b, k))? * (y + y - E::one()) + (E::one() - y));
                }
                s0 = s0 + tt;
            }
            let s0 = eq_pts(&sc_f.r[..lt as usize], pi, lt as usize)
                * eq_pts(
                    &sc_f.r[lt as usize..lt as usize + lgk as usize],
                    pg,
                    lgk as usize,
                )
                * s0;
            scd.row_u = psc_row(&mut f, &mut scd.p, s0, &Aff::default())?;
        }
        let om5 = tr_batch(tr, self.np, calls_hc)?;
        let mut sc_h = sc3_in(
            &mut f,
            tr,
            &mut slot,
            self.nv_h(),
            self.np,
            &Aff::constant(E::zero()),
            calls_hc,
        )?;
        {
            let ri2 = &sc_h.r[..lt as usize];
            let rg2 = &sc_h.r[lt as usize..lt as usize + lgk as usize];
            let rk = &sc_h.r[lt as usize + lgk as usize..];
            let f_h = eq_pts(&tbi, ri2, lt as usize)
                * eq_pts(&tbg, rg2, lgk as usize)
                * eq_pts(&tk, rk, 4);
            let wh: Vec<E> = (0..self.np).map(|b| om5[b] * f_h).collect();
            sc3_row(&mut f, &mut sc_h, &wh, "h")?;
        }
        // Step 8: the commitment to U3.
        gate.root_in_h(&mut f, tr, &[self.seam.i_u3() as i32], calls_hc)?;
        let la = 1u64 << cf.la;
        let m_s = 1u64 << lm_s;
        let s2 = 1u64 << ls;
        let gso = self.a.fill_o * t >> cf.la;
        let gsq = self.a.fill_q * t >> cf.la;
        let mb = 1u64 << cf.lmb;
        let k_as = self.a.k_as;
        let k_part = k_as / cf.n_as;
        let kb_a = self.a.kb_a;
        let i_ah = cf.n_as as i32;
        let i_ao = i_ah + 1;
        let i_ba = i_ah + 2;
        let i_qa = i_ah + 3;
        let mut fun: Vec<HFun> = Vec::new();
        let mut tab_len: BTreeMap<u64, u64> = BTreeMap::new();
        let mut p_at = 0u64;
        // The helpers below are free functions taking the mutable pieces explicitly.
        fn add_tab(
            tl: &mut super::smallness::HTailF2,
            f: &HFork,
            fun: &mut Vec<HFun>,
            tab_len: &mut BTreeMap<u64, u64>,
            p_at: &mut u64,
            m: i32,
            l: u64,
            phi: &[E],
            elems: u64,
            nm: &str,
        ) -> Result<u64> {
            let at = *p_at;
            tl.fun_open()?;
            if m < 0
                || m as usize >= tl.mats.len()
                || l == 0
                || tl.mats[m as usize].m % l != 0
                || elems != tl.mats[m as usize].k * (tl.mats[m as usize].m / l)
            {
                return Err(Refusal::internal(&format!("{}internal-a-table-length", f.g)));
            }
            fun.push(HFun {
                m,
                l,
                phi: phi.to_vec(),
                tree: 2,
                at,
                name: format!("{}{}", f.g, nm),
            });
            tab_len.insert(at, elems);
            *p_at += elems;
            Ok(at)
        }
        fn add_as(
            tl: &mut super::smallness::HTailF2,
            f: &HFork,
            fun: &mut Vec<HFun>,
            tab_len: &mut BTreeMap<u64, u64>,
            p_at: &mut u64,
            phi: &[E],
            nm: &str,
            n_as: u64,
            m_s: u64,
            k_part: u64,
        ) -> Result<u64> {
            let at = *p_at;
            for q in 0..n_as {
                add_tab(
                    tl,
                    f,
                    fun,
                    tab_len,
                    p_at,
                    q as i32,
                    m_s,
                    phi,
                    k_part,
                    &format!("{}-part{}", nm, q),
                )?;
            }
            tab_len.insert(at, *p_at - at);
            Ok(at)
        }
        fn last_n(z: &[E], n: usize) -> Vec<E> {
            eq_tab(&z[z.len() - n..], n)
        }
        // `tok(hi, lo)`: B = 2^lB and T from the shape.
        let tok = |hi: &[E], lo: &[E], b: u64, t_count: u64| -> Vec<E> {
            let el = eq_tab(lo, b.trailing_zeros() as usize);
            let mut v = vec![E::zero(); t_count as usize];
            for ii in 0..(t_count / b) {
                for xx in 0..b {
                    v[(ii * b + xx) as usize] = hi[ii as usize] * el[xx as usize];
                }
            }
            v
        };
        let lng = |zc: &[E], ptk: &[E], ldh: i32, ls: i32, la: u64, s2: u64, t_count: u64| -> Result<Vec<E>> {
            if ptk.len() as u64 != t_count || la != s2 * t_count {
                return Err(Refusal::named("plan-tensor-layout"));
            }
            let k = cut_last(zc, ldh as usize, ls as usize)?;
            Ok(block_rows(&eq_tab(k.lo, ls as usize), ptk))
        };
        // `ptM.insert(ptM.end(), zilo, zilo + lB)`: exactly lB entries of zi_lo, not all of them.
        let pt_m = {
            let mut v = vpm.r[..(lgk + 2 * ln_t - 1) as usize].to_vec();
            v.extend_from_slice(&zi_lo[..cf.l_b as usize]);
            v.extend_from_slice(&vpm.r[vpm.r.len() - cf.l_b as usize..]);
            v
        };
        let pt_d = {
            let mut v = vpd.r[..(lgk + ln_t) as usize].to_vec();
            v.extend_from_slice(&zi_lo[..cf.l_b as usize]);
            v.extend_from_slice(&vpd.r[vpd.r.len() - cf.l_b as usize..]);
            v
        };
        for pc in &pcl {
            for i in 1..=lm_s as usize {
                if pc.z[pc.z.len() - i] != g1.zx[g1.zx.len() - i] {
                    return Err(Refusal::internal(&format!("{}internal-a-merged-point", f.g)));
                }
            }
        }
        let t_a = add_as(
            &mut self.seam.tl,
            &f,
            &mut fun,
            &mut tab_len,
            &mut p_at,
            &last_n(&g1.zx, lm_s as usize),
            "as@zx",
            cf.n_as,
            m_s,
            k_part,
        )?;
        let t_vm = add_as(
            &mut self.seam.tl,
            &f,
            &mut fun,
            &mut tab_len,
            &mut p_at,
            &last_n(&pt_m, lm_s as usize),
            "as@VPM",
            cf.n_as,
            m_s,
            k_part,
        )?;
        let t_vd = add_as(
            &mut self.seam.tl,
            &f,
            &mut fun,
            &mut tab_len,
            &mut p_at,
            &last_n(&pt_d, lm_s as usize),
            "as@VPD",
            cf.n_as,
            m_s,
            k_part,
        )?;
        for k in &mut kfs {
            let phi = tok(&k.wi, &k.zi, 1u64 << cf.l_b, t);
            k.t_m = add_tab(
                &mut self.seam.tl,
                &f,
                &mut fun,
                &mut tab_len,
                &mut p_at,
                i_ah,
                t,
                &phi,
                self.a.fill_h,
                &format!(
                    "ah@phiM-{}{}",
                    self.a.calls[k.call].c.name,
                    if k.seg == S_FD { "-D" } else { "-M" }
                ),
            )?;
        }
        let h_w = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_ah, t, &eq_tab(zi_w, lt as usize), self.a.fill_h, "ah@ziW")?;
        let h_x = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_ah, t, &eq_tab(zi_x, lt as usize), self.a.fill_h, "ah@ziX")?;
        let h_e = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_ah, t, &eq_tab(&sc_e.r[lgk as usize..], lt as usize), self.a.fill_h, "ah@riE")?;
        let h_t = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_ah, t, &eq_tab(&ti, lt as usize), self.a.fill_h, "ah@ti")?;
        let h_pi = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_ah, t, &eq_tab(pi, lt as usize), self.a.fill_h, "ah@pi")?;
        let h_r2 = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_ah, t, &eq_tab(&sc_h.r[..lt as usize], lt as usize), self.a.fill_h, "ah@ri2")?;
        for i in 0..(lt + ldh) as usize {
            if zi_w[i] != zi_h[i] || zi_w[i] != g1.zx[g1.zx.len() - (lt + ldh) as usize + i] {
                return Err(Refusal::internal(&format!("{}internal-a-merged-point", f.g)));
            }
        }
        let t_o = add_tab(
            &mut self.seam.tl,
            &f,
            &mut fun,
            &mut tab_len,
            &mut p_at,
            i_ao,
            la,
            &lng(zc_w, &eq_tab(zi_w, lt as usize), ldh, ls, la, s2, t)?,
            gso,
            "ao@zx",
        )?;
        for k in &mut kfs {
            let (wi_r, wj_r) = if k.seg == S_FM {
                let mut wi_r = vec![E::zero(); n_t as usize];
                let mut wj_r = vec![E::zero(); n_t as usize];
                let e_p = eq_tab(&k.sc.r[lgk as usize..], ln_t as usize - 1);
                let es = eq_tab(&k.sc.r[lgk as usize + ln_t as usize - 1..], ln_t as usize);
                for pp in 0..h_p {
                    for sg in 0..n_t - 1 {
                        let (ii, jj) = self.a.cover(pp, sg);
                        wi_r[ii as usize] = wi_r[ii as usize] + e_p[pp as usize] * es[sg as usize];
                        wj_r[jj as usize] = wj_r[jj as usize] + e_p[pp as usize] * es[sg as usize];
                    }
                }
                (wi_r, wj_r)
            } else {
                let e = eq_tab(&k.sc.r[lgk as usize..], ln_t as usize);
                (e.clone(), e)
            };
            let rc_k = &k.sc.r[k.sc.r.len() - ldh as usize..];
            k.t_q = add_tab(
                &mut self.seam.tl,
                &f,
                &mut fun,
                &mut tab_len,
                &mut p_at,
                i_qa,
                la,
                &lng(rc_k, &tok(&wi_r, &k.zi, 1u64 << cf.l_b, t), ldh, ls, la, s2, t)?,
                gsq,
                &format!("qa@phiQ-{}", self.a.calls[k.call].c.name),
            )?;
            k.t_k = add_tab(
                &mut self.seam.tl,
                &f,
                &mut fun,
                &mut tab_len,
                &mut p_at,
                i_qa,
                la,
                &lng(rc_k, &tok(&wj_r, &k.zj, 1u64 << cf.l_b, t), ldh, ls, la, s2, t)?,
                gsq,
                &format!("qa@phiK-{}", self.a.calls[k.call].c.name),
            )?;
        }
        let q_o = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_qa, la, &lng(zc_w, &eq_tab(&sc_e.r[lgk as usize..], lt as usize), ldh, ls, la, s2, t)?, gsq, "qa@o")?;
        let q_vm = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_qa, la, &lng(zc_w, &tok(&wjv, &vpm.r[vpm.r.len() - cf.l_b as usize..], 1u64 << cf.l_b, t), ldh, ls, la, s2, t)?, gsq, "qa@VPM")?;
        let q_vd = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_qa, la, &lng(zc_w, &tok(&eq_tab(&vpd.r[lgk as usize..], ln_t as usize), &vpd.r[vpd.r.len() - cf.l_b as usize..], 1u64 << cf.l_b, t), ldh, ls, la, s2, t)?, gsq, "qa@VPD")?;
        let rc = &sc_f.r[lt as usize + lgk as usize..];
        let q_f = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_qa, la, &lng(rc, &eq_tab(&sc_f.r[..lt as usize], lt as usize), ldh, ls, la, s2, t)?, gsq, "qa@f-q")?;
        let q_kx = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_qa, la, &lng(rc, &eq_tab(pj, lt as usize), ldh, ls, la, s2, t)?, gsq, "qa@f-kx")?;
        let t_bit = [
            add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_ba, mb, &forest_phi_b(&g1, cf.lmb, 0)?, kb_a, "bA-bits-0")?,
            add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_ba, mb, &forest_phi_b(&g1, cf.lmb, 1)?, kb_a, "bA-bits-1")?,
        ];
        let t_pin = add_tab(&mut self.seam.tl, &f, &mut fun, &mut tab_len, &mut p_at, i_ba, mb, &forest_phi_p(cf.lmb), kb_a, "bA-pin")?;
        if p_at != self.n_w {
            return Err(Refusal::internal(&format!("{}internal-af-W-length", f.g)));
        }
        self.seam.tl.close_funs(&fun)?;
        // Step 9.
        self.seam
            .transcript(&mut f, tr, &mut slot, gate, calls_hc)?;
        if slot != self.n_msg as u32 {
            return Err(Refusal::internal(&format!("{}internal-slot-count", f.g)));
        }
        // Step 10.
        f.plan_claims = self.n_lin as u32;
        self.seam.batch(&mut f, tr, slot, gate, calls_hc)?;
        {
            let i_u3 = self.seam.i_u3();
            let m1 = E::zero() - E::one();
            let mut kf: Vec<Aff> = vec![Aff::default(); self.nc];
            let mut joined = vec![0u8; self.nc];
            forest_objects(&mut f, &g1)?;
            let lin_planes = |f: &mut HFork, pc: &PlaneClaim| -> Result<()> {
                for x in 0..pc.np {
                    let mut ff = s_aff(pc.s0 + x as u32);
                    for w in &pc.pw {
                        let pl = plane(
                            f,
                            i_u3,
                            &tab_len,
                            t_a,
                            x,
                            w.lam,
                            w.a,
                            &pc.z,
                            pc.is_d,
                            n_m,
                            n_d,
                            lm_s,
                            lam,
                            ha,
                        )?;
                        ff.add(&pl, m1 * w.wp);
                    }
                    f.lin(&ff)?;
                }
                Ok(())
            };
            // Claim 3: KR.
            for q in 0..self.nc {
                if self.a.calls[q].kind != "KR" {
                    continue;
                }
                let mut v = Aff::default();
                for pc in &pcl {
                    if pc.call != q {
                        continue;
                    }
                    lin_planes(&mut f, pc)?;
                    let lw = sum_w(&pc.pw);
                    let l128 = e_scale(lw, 128);
                    let mut t1 = s_aff(pc.s0);
                    t1.add(&Aff::constant(l128), E::one());
                    let mut t2 = s_aff(pc.s0 + 1);
                    t2.add(&Aff::constant(l128), E::one());
                    v.add(&t1, E::one());
                    v.add(&t2, ei(1i64 << 20));
                    v.add(&s_aff(pc.s0 + 2), ei(1i64 << 40));
                }
                kf[q] = v;
                joined[q] += 1;
            }
            // Claim 4: KFD.
            for q in 0..self.nc {
                if self.a.calls[q].kind != "KFD" {
                    continue;
                }
                let c = &self.a.calls[q];
                let dd = self.a.shd(c.sh);
                let mut wall = E::zero();
                for pc in &c.pcs {
                    wall = wall
                        + eq_at(&c.c.zk, (c.c.n - pc.b) as usize, pc.off >> pc.b);
                }
                let mut v = Aff::constant(e_scale(E::one() - wall, c.c.tau_at(c.c.t0)));
                for k in kfs.iter().filter(|k| k.call == q) {
                    let s = k.s0;
                    lin_planes(&mut f, &pcl[k.claim])?;
                    {
                        let mut ff = s_aff(s + 5);
                        for w in &k.pw {
                            let sg = over_g(&k.zg, lgk as usize, g, |gg| {
                                sh_v(
                                    &f,
                                    i_u3,
                                    &tab_len,
                                    k.t_m,
                                    self.a.o_mr,
                                    4,
                                    h,
                                    w.lam,
                                    gg * ha + w.a,
                                    self.a.lam,
                                )
                            })?;
                            ff.add(&sg, m1 * w.wp);
                        }
                        f.lin(&ff)?;
                    }
                    f.lin(&k.sc.row_u)?;
                    let rg_k = &k.sc.r[..lgk as usize];
                    let rc_k = &k.sc.r[k.sc.r.len() - ldh as usize..];
                    for b in 0..k.pw.len() {
                        let w = &k.pw[b];
                        let a_side = over_g(rg_k, lgk as usize, g, |gg| {
                            xl(
                                &f,
                                i_u3,
                                &tab_len,
                                k.t_q,
                                &self.a.at_q,
                                w.lam,
                                gg * ha + w.a,
                                rc_k,
                                dh,
                                ls,
                                s2,
                            )
                        })?;
                        f.lin(&(sc3_a(&k.sc, b) - a_side))?;
                        let b_side = over_g(rg_k, lgk as usize, g, |gg| {
                            xl(
                                &f,
                                i_u3,
                                &tab_len,
                                k.t_k,
                                &self.a.at_k,
                                w.lam,
                                gg,
                                rc_k,
                                dh,
                                ls,
                                s2,
                            )
                        })?;
                        f.lin(&(sc3_b(&k.sc, b) - b_side))?;
                    }
                    let lw = sum_w(&k.pw);
                    let l128 = e_scale(lw, 128);
                    let dp = if k.seg == S_FM {
                        let mut dp = s_aff(s + 5);
                        dp.add(&s_aff(s + 6), E::zero() - E::one());
                        dp.add(
                            &Aff::constant(e_scale(lw, dd.c) * ones_of(&k.z_s, ln_t as usize)),
                            E::one(),
                        );
                        dp
                    } else {
                        let mut dp = s_aff(s + 5);
                        dp.add(&s_aff(s + 6), E::zero() - E::one());
                        dp.add(
                            &Aff::constant(
                                e_scale(lw, dd.om) * (E::one() - le_of(&k.zj, &k.zi, cf.l_b as usize)),
                            ),
                            E::one(),
                        );
                        dp
                    };
                    let mut t1 = s_aff(s);
                    t1.add(&Aff::constant(l128), E::one());
                    let mut t2 = s_aff(s + 1);
                    t2.add(&Aff::constant(l128), E::one());
                    let mut t3 = s_aff(s + 3);
                    t3.add(&Aff::constant(l128), E::one());
                    let mut term = dp;
                    term = term - t1;
                    let t2s = t2 * ei(256);
                    term = term - t2s;
                    term = term + (s_aff(s + 2) * ei(1i64 << 32));
                    let mut t34 = t3;
                    t34 = t34 + (s_aff(s + 4) * ei(256));
                    term = term + (t34 * ei(1i64 << 33));
                    v = v + term;
                }
                kf[q] = v;
                joined[q] += 1;
            }
            // Claim 5.
            {
                let mut zc_ = s_aff(s_zc);
                let mut rh = s_aff(s_rh);
                let mut rhp = s_aff(s_rhp);
                let mut r2 = s_aff(s5h);
                let mut r2p = s_aff(s5h + 1);
                for w in &pw_w {
                    let sv = over_g(zg_w, lgk as usize, g, |gg| {
                        sh_v(
                            &f,
                            i_u3,
                            &tab_len,
                            h_w,
                            self.a.o_zr,
                            4,
                            h,
                            w.lam,
                            gg * ha + w.a,
                            self.a.lam,
                        )
                    })?;
                    zc_.add(&sv, m1 * w.wp);
                    let rhv = over_g(zg_w, lgk as usize, g, |gg| {
                        xl(
                            &f,
                            i_u3,
                            &tab_len,
                            t_o,
                            &TenAt { off: self.a.o_rh, nl: 1, cnt: lam, j: dq },
                            w.lam,
                            gg * ha + w.a,
                            zc_w,
                            dh,
                            ls,
                            s2,
                        )
                    })?;
                    rh.add(&rhv, m1 * w.wp);
                    let rhpv = over_g(zg_w, lgk as usize, g, |gg| {
                        xl(
                            &f,
                            i_u3,
                            &tab_len,
                            t_o,
                            &TenAt { off: self.a.o_rhp, nl: 1, cnt: lam, j: dq },
                            w.lam,
                            gg * ha + w.a,
                            zc_w,
                            dh,
                            ls,
                            s2,
                        )
                    })?;
                    rhp.add(&rhpv, m1 * w.wp);
                }
                for w in &pw_h {
                    let r2v = over_g(zg_h, lgk as usize, g, |gg| {
                        xl(
                            &f,
                            i_u3,
                            &tab_len,
                            t_o,
                            &TenAt { off: self.a.o_rh, nl: 1, cnt: lam, j: dq },
                            w.lam,
                            gg * ha + w.a,
                            zc_h,
                            dh,
                            ls,
                            s2,
                        )
                    })?;
                    r2.add(&r2v, m1 * w.wp);
                    let r2pv = over_g(zg_h, lgk as usize, g, |gg| {
                        xl(
                            &f,
                            i_u3,
                            &tab_len,
                            t_o,
                            &TenAt { off: self.a.o_rhp, nl: 1, cnt: lam, j: dq },
                            w.lam,
                            gg * ha + w.a,
                            zc_h,
                            dh,
                            ls,
                            s2,
                        )
                    })?;
                    r2p.add(&r2pv, m1 * w.wp);
                }
                f.lin(&zc_)?;
                f.lin(&rh)?;
                f.lin(&rhp)?;
                for k in 0..lt {
                    let mut ff = s_aff(s_ib + k as u32);
                    for w in &pw_x {
                        let sv = over_g(zg_x, lgk as usize, g, |gg| {
                            sh_v(
                                &f,
                                i_u3,
                                &tab_len,
                                h_x,
                                self.a.o_ib,
                                1,
                                lt as u64 * h,
                                w.lam,
                                k as u64 * h + gg * ha + w.a,
                                self.a.lam,
                            )
                        })?;
                        ff.add(&sv, m1 * w.wp);
                    }
                    f.lin(&ff)?;
                }
                f.lin(&r2)?;
                f.lin(&r2p)?;
                let rem = s_aff(s_acc) * ei(2) + s_aff(s_zc) - s_aff(s_zo) * ei(2);
                let mut ib = Aff::default();
                for k in 0..lt {
                    ib.add(&s_aff(s_ib + k as u32), ei(1i64 << k));
                }
                let mut tw0 = rem.clone();
                let mut rh128 = s_aff(s_rh);
                rh128.add(&Aff::constant(e_scale(lww, 128)), E::one());
                tw0 = tw0 - (rh128 * ei(65536));
                let mut tw1 = s_aff(s_zc) * ei(2);
                tw1 = tw1 - Aff::constant(lww);
                tw1 = tw1 - rem;
                let mut rhp128 = s_aff(s_rhp);
                rhp128.add(&Aff::constant(e_scale(lww, 128)), E::one());
                tw1 = tw1 - (rhp128 * ei(65536));
                let twl = tw0 * (E::one() - zsl) + tw1 * zsl;
                let tix = (Aff::constant(lwx * id_of(zi_x, lt as usize)) - ib) * ei(1i64 << (16 - lt));
                for q in 0..self.nc {
                    if self.a.calls[q].kind != "R16" {
                        continue;
                    }
                    let mut v = Aff::default();
                    if Self::holds(&self.a.calls[q], S_WL) {
                        v.add(&twl, E::one());
                    }
                    if Self::holds(&self.a.calls[q], S_IX) {
                        v.add(&tix, E::one());
                    }
                    kf[q] = v;
                    joined[q] += 1;
                }
                let mut whv = s_aff(s5h);
                whv.add(&Aff::constant(e_scale(lwh, 128)), E::one());
                let mut wh2 = s_aff(s5h + 1);
                wh2.add(&Aff::constant(e_scale(lwh, 128)), E::one());
                kf[qw] = whv + (wh2 * ei(1i64 << 20));
                joined[qw] += 1;
                f.lin(&sc_e.row_u)?;
                let rg_e = &sc_e.r[..lgk as usize];
                for b in 0..self.np {
                    let w = &pw_w[b];
                    let a_side = over_g(rg_e, lgk as usize, g, |gg| {
                        sh_v(
                            &f,
                            i_u3,
                            &tab_len,
                            h_e,
                            self.a.o_zr,
                            4,
                            h,
                            w.lam,
                            gg * ha + w.a,
                            self.a.lam,
                        )
                    })?;
                    f.lin(&(sc3_a(&sc_e, b) - a_side))?;
                    let b_side = over_g(rg_e, lgk as usize, g, |gg| {
                        xl(
                            &f,
                            i_u3,
                            &tab_len,
                            q_o,
                            &self.a.at_o,
                            w.lam,
                            gg * ha + w.a,
                            zc_w,
                            dh,
                            ls,
                            s2,
                        )
                    })?;
                    f.lin(&(sc3_b(&sc_e, b) - b_side))?;
                }
            }
            for &j in &joined {
                if j != 1 {
                    return Err(Refusal::named("af-unclosed-call"));
                }
            }
            // The keys that no weighed piece covers must match each tree's padding count.
            {
                let mut laid = vec![0u64; g1.nt as usize];
                for q in 0..self.nc {
                    let c = &self.a.calls[q];
                    if c.kind != "KFD" && c.c.tau_at(c.c.t0) != 0 {
                        return Err(Refusal::internal(&format!("{}internal-af-padding-key", f.g)));
                    }
                    let mut upto = 0u64;
                    for i in 0..c.pcs.len() {
                        if !weighed[q][i] {
                            forest_pub_run(
                                &g1,
                                &mut laid,
                                q as i32,
                                c.pcs[i].off,
                                1u64 << c.pcs[i].b,
                            )?;
                            continue;
                        }
                        upto = upto.max(c.pcs[i].off + (1u64 << c.pcs[i].b));
                    }
                    forest_pub_run(&g1, &mut laid, q as i32, upto, (1u64 << c.c.n) - upto)?;
                }
                forest_padding_laid(&g1, &laid)?;
            }
            f.lin(&forest_join(&g1, &kf)?)?;
            // Claim 6.
            f.lin(&(s_aff(s_cl) + s_aff(s_cl + 1) - s_aff(s_acc) - s_aff(s_zc) * gam_p[1]))?;
            f.lin(&vpm.row_u)?;
            for b in 0..self.np {
                let w = &pw_w[b];
                let av = plane(&f, i_u3, &tab_len, t_vm, 3, w.lam, w.a, &pt_m, false, n_m, n_d, lm_s, lam, ha)?;
                let mut av2 = av;
                av2.add(&Aff::constant(ei(128)), E::one());
                let bv = plane(&f, i_u3, &tab_len, t_vm, 4, w.lam, w.a, &pt_m, false, n_m, n_d, lm_s, lam, ha)?;
                av2 = av2 + (bv * ei(256));
                f.lin(&(sc3_a(&vpm, b) - av2))?;
                let bs = over_g(&vpm.r[..lgk as usize], lgk as usize, g, |gg| {
                    xl(
                        &f,
                        i_u3,
                        &tab_len,
                        q_vm,
                        &self.a.at_v,
                        w.lam,
                        gg,
                        zc_w,
                        dh,
                        ls,
                        s2,
                    )
                })?;
                f.lin(&(sc3_b(&vpm, b) - (Aff::constant(gam_p[1]) + bs)))?;
            }
            f.lin(&vpd.row_u)?;
            for b in 0..self.np {
                let w = &pw_w[b];
                let av = plane(&f, i_u3, &tab_len, t_vd, 3, w.lam, w.a, &pt_d, true, n_m, n_d, lm_s, lam, ha)?;
                let mut av2 = av;
                av2.add(&Aff::constant(ei(128)), E::one());
                let bv = plane(&f, i_u3, &tab_len, t_vd, 4, w.lam, w.a, &pt_d, true, n_m, n_d, lm_s, lam, ha)?;
                av2 = av2 + (bv * ei(256));
                f.lin(&(sc3_a(&vpd, b) - av2))?;
                let bs = over_g(&vpd.r[..lgk as usize], lgk as usize, g, |gg| {
                    xl(
                        &f,
                        i_u3,
                        &tab_len,
                        q_vd,
                        &self.a.at_v,
                        w.lam,
                        gg,
                        zc_w,
                        dh,
                        ls,
                        s2,
                    )
                })?;
                f.lin(&(sc3_b(&vpd, b) - (Aff::constant(gam_p[1]) + bs)))?;
            }
            // Claim 7.
            for b in 0..self.np {
                let lam_b = b / ha as usize;
                let a_b = b % ha as usize;
                let sv = over_g(&tg, lgk as usize, g, |gg| {
                    sh_v(
                        &f,
                        i_u3,
                        &tab_len,
                        h_t,
                        self.a.o_mr,
                        4,
                        h,
                        lam_b as u64,
                        gg * ha + a_b as u64,
                        self.a.lam,
                    )
                })?;
                f.lin(&(s_aff(s_m6 + b as u32) - sv))?;
            }
            f.lin(&sc_f.row_u)?;
            for b in 0..self.np {
                let lam_b = b / ha as usize;
                let a_b = b % ha as usize;
                let sv = over_g(&sc_f.r[lt as usize..lt as usize + lgk as usize], lgk as usize, g, |gg| {
                    xl(
                        &f,
                        i_u3,
                        &tab_len,
                        q_f,
                        &self.a.at_q,
                        lam_b as u64,
                        gg * ha + a_b as u64,
                        rc,
                        dh,
                        ls,
                        s2,
                    )
                })?;
                f.lin(&(sc3_a(&sc_f, b) - sv))?;
            }
            {
                f.lin(&scd.row_u)?;
                for lam_v in 0..lam {
                    let sv = over_g(pg, lgk as usize, g, |gg| {
                        xl(
                            &f,
                            i_u3,
                            &tab_len,
                            q_kx,
                            &self.a.at_k,
                            lam_v,
                            gg,
                            rc,
                            dh,
                            ls,
                            s2,
                        )
                    })?;
                    f.lin(&(s_aff(s_kc + lam_v as u32) - sv))?;
                }
                for b in 0..self.np {
                    let lam_b = b / ha as usize;
                    let a_b = b % ha as usize;
                    for k in 0..lt {
                        let sv = over_g(pg, lgk as usize, g, |gg| {
                            sh_v(
                                &f,
                                i_u3,
                                &tab_len,
                                h_pi,
                                self.a.o_ib,
                                1,
                                lt as u64 * h,
                                lam_b as u64,
                                k as u64 * h + gg * ha + a_b as u64,
                                self.a.lam,
                            )
                        })?;
                        f.lin(&(s_aff(s_ib_at(b, k)) - sv))?;
                    }
                }
            }
            // Claim 8.
            f.lin(&sc_h.row_u)?;
            {
                let ek = eq_tab(&sc_h.r[lt as usize + lgk as usize..], 4);
                for b in 0..self.np {
                    let lam_b = b / ha as usize;
                    let a_b = b % ha as usize;
                    f.lin(&(sc3_b(&sc_h, b) - sc3_a(&sc_h, b) + Aff::constant(E::one())))?;
                    let mut ff = sc3_a(&sc_h, b);
                    for k in 0..lt {
                        let sv = over_g(&sc_h.r[lt as usize..lt as usize + lgk as usize], lgk as usize, g, |gg| {
                            sh_v(
                                &f,
                                i_u3,
                                &tab_len,
                                h_r2,
                                self.a.o_ib,
                                1,
                                lt as u64 * h,
                                lam_b as u64,
                                k as u64 * h + gg * ha + a_b as u64,
                                self.a.lam,
                            )
                        })?;
                        ff.add(&sv, m1 * ek[k as usize]);
                    }
                    f.lin(&ff)?;
                }
            }
            // Claim 9.
            {
                let w = (g1.k_t + 5 - cf.lmb) as usize;
                let mut at = [Aff::default(), Aff::default()];
                for e in 0..2usize {
                    let ec = eq_tab(&g1.zb[e][g1.k_t as usize..], g1.c_k as usize);
                    let et = eq_tab(&g1.zb[e], w);
                    for cc in 0..self.nc {
                        for th in 0..(1usize << w) {
                            let col = (cc << w) + th;
                            let tb = u3_at(&f, i_u3, &tab_len, t_bit[e], col as u64)?;
                            at[e].add(&tb, ec[cc] * et[th]);
                        }
                    }
                }
                let mut f0 = Aff::constant(E::zero() - eb((1u64 << g1.v()) - g1.padding()));
                for col in 0..((self.nc as u64) << w) {
                    f0.add(&u3_at(&f, i_u3, &tab_len, t_pin, col)?, E::one());
                }
                let leaves_a = g1.leaves_a;
                let c0 = psc_row(&mut f, &mut g1.leaves, E::one(), &(at[0].clone() * leaves_a))?;
                f.lin(&c0)?;
                f.lin(&(Aff::slot(g1.s_bit) - at[1].clone()))?;
                f.lin(&f0)?;
                forest_planes_added(&g1)?;
            }
            self.seam.objects(&mut f, &fun)?;
            for j in 0..self.n_msg {
                if f.ls[j].is_zero() {
                    return Err(Refusal::internal(&format!("{}internal-a-free-slot", f.g)));
                }
            }
            self.seam.tl.funs_held(&f, &fun)?;
        }
        self.seam.finish(&mut f, tr, gate, calls_hc)?;
        if f.n_claim != f.plan_claims {
            return Err(Refusal::internal(&format!("{}internal-f-draws", f.g)));
        }
        f.kap_all_taken()?;
        self.seam.tl.fold_all_taken(&f)?;
        self.n_claim = f.n_claim;
        if self.n_claim as usize != self.n_lin {
            return Err(Refusal::internal(&format!("{}internal-a-claim-count", f.g)));
        }
        if self.seam.tl.fold_drawn != 1 {
            return Err(Refusal::internal(&format!("{}internal-af-rows-booked", f.g)));
        }
        if 1 + self.seam.tl.groups_run() != 2 {
            return Err(Refusal::internal(&format!("{}internal-a-calls-booked", f.g)));
        }
        Ok(())
    }
}

/// `AFork::segB(seg)` as the call stores it in every piece of that segment.
fn seg_len(c: &ACall, seg: i32) -> u64 {
    c.pcs.iter().find(|p| p.seg == seg).map(|p| p.b as u64).unwrap_or(0)
}
