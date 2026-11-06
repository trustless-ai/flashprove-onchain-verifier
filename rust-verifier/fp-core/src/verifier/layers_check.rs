//! Checks one layer sub-proof G_g, ported from `verifier/src/vf_layers_check.inc` (the
//! `runForkHidG2` lambda): the lookup forest, the norms' digit rows, the two token sumchecks, the
//! gated products, the weight claims and the approximate range check, in the order of
//! docs/format/11-2-feed-forward-segment.md.
//!
//! C++ keeps its lambdas with captured `Ex`/`Aff` values; the port precomputes each panel's two
//! factors into vectors, because a Rust closure cannot borrow the fork, the tables and the claims
//! list at once. The segment calls that C++ reaches through `currentSegment` go through
//! [`AttentionSegment`] (the same `t2Batch`/`doorH` seam that the attention sub-proof uses).

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::codes::ceil_log2;
use crate::refusal::{Refusal, Result};

use super::attention_check::AttentionSegment;
use super::attention_shape::{
    cut_last, head_feat, hi_tab, last_of, long_phi, long_point, ten_cell,
};
use super::common::{eq_tab, fint, order_default, order_range};
use super::engine::{fill_l, layer_object, read_product_level_rounds, Aff, HFork, ProductLevel};
use super::layers_plan::{HPlan2, Reads};
use super::lookup::{forest_join_added, forest_objects, forest_pad, forest_plane_lins, u_ent, HForest, HFun};
use super::norm_digit_rows::{
    led_carry5, led_lines5, led_no, led_np, led_nr, led_ns, led_products5, led_mu, row5, Row5,
};
use super::packing::e_scale;
use super::segment::{eq_low, eq_low_at};
use super::smallness::HTailF2;
use super::stage_context::{kl, kl_m, rope_c, LKD, LKG, LKQ, LM1, LM2};
use super::stage_layout::{Hdr, Lay, KDD, KGD, KUD, KR_};
use super::stage_layout::{KQ_, KV_, KO_};
use super::sumcheck::{psc_begin, psc_ends, psc_row, tsc_in, TokenSumcheckState};
use super::transcript::{tr_batch, tr_point, RoundName, Tr};
use super::weights_layout::{ws_fork_end, WsClaim, WsFac, WsForkOut, WsLay};
use super::weights_merge::ws_fork_lin;

fn ei(v: i64) -> E {
    E::from_base(crate::field::ext::F::from_u64(fint(v)))
}

/// `pw(k)`: `2^k` in E.
fn pw(k: u32) -> E {
    ei(1i64 << k)
}

fn eb(v: u64) -> E {
    E::from_base(crate::field::ext::F::from_u64(v))
}

/// What one row of a norm's digit table (four limbs) holds, as forms (`RowA`).
#[derive(Clone)]
struct RowA {
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

impl Default for RowA {
    fn default() -> Self {
        RowA {
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

/// The inputs of one layer sub-proof's check.
pub struct LayerCheckInputs<'a> {
    pub h: &'a Hdr,
    pub y: &'a Lay,
    pub plan: &'a HPlan2,
    pub reads: &'a Reads,
    pub ws_lay: &'a WsLay,
    pub kl: &'a [u32],
    pub g: u64,
    pub ngr: u64,
    pub p3: bool,
    pub lidb: i32,
    pub limbs: i32,
    pub gcl: i32,
    pub rcl: i32,
    /// The request's token vector (`so.req[..T]`), for the embedding's claim in G_0.
    pub tokens: &'a [u32],
}

/// What the run hands the request frame.
pub struct LayerRunOut {
    pub wo: WsForkOut,
    pub nc: usize,
    pub nm: usize,
    pub n_claim: u32,
    pub n_slots: u32,
}

/// `mname[4]`.
const MNAME: [&str; 4] = ["af", "ad", "ar", "qa"];

fn zl(c: &super::stage_layout::CallD) -> &[E] {
    &c.c.zk
}

fn zj(c: &super::stage_layout::CallD, ll: u32) -> &[E] {
    &c.c.zk[ll as usize..]
}

fn call_of<'a>(y: &'a Lay, sn: &str) -> Result<&'a super::stage_layout::CallD> {
    for c in &y.calls {
        for s in &c.segs {
            if s.name == sn {
                return Ok(c);
            }
        }
    }
    Err(Refusal::internal(&format!("internal-segment-{}", sn)))
}

fn call_no(y: &Lay, cn: &str) -> Result<usize> {
    for (q, c) in y.calls.iter().enumerate() {
        if c.c.name == cn {
            return Ok(q);
        }
    }
    Err(Refusal::internal(&format!("internal-call-{}", cn)))
}

fn sum_e(v: &[E]) -> E {
    let mut s = E::zero();
    for &x in v {
        s = s + x;
    }
    s
}

fn sum_r(v: &[E], a: u64, b: u64) -> E {
    let mut s = E::zero();
    for i in a..b {
        s = s + v[i as usize];
    }
    s
}

/// `tabAt(name)`.
fn tab_at(tab: &BTreeMap<String, u64>, n: &str) -> Result<u64> {
    tab.get(n)
        .copied()
        .ok_or_else(|| Refusal::internal(&format!("internal-table-{}", n)))
}

/// `U3at(t, i)`.
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
            "{}internal-g-table-index",
            f.g
        ))),
    }
}

/// `shortA(t, X, i, j)`: a short table's entry for row i, column j, limbs at radix 256.
fn short_a(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    t: u64,
    x: &super::stage_layout::Ten,
    i: u64,
    j: u64,
) -> Result<Aff> {
    let mut s = Aff::default();
    let mut sc = 1u64;
    for l in 0..x.nl as u64 {
        s = s + u3_at(f, i_u3, tab_len, t, ten_cell(&x.at(), l, i, j))? * ei(sc as i64);
        sc *= 256;
    }
    Ok(s)
}

/// `longA(t, X, i, jh)`: a long table's entry, a block of S2 features per index.
fn long_a(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    t: u64,
    x: &super::stage_layout::Ten,
    s2: u64,
    i: u64,
    jh: u64,
) -> Result<Aff> {
    let mut s = Aff::default();
    let mut sc = 1u64;
    for l in 0..x.nl as u64 {
        s = s + u3_at(f, i_u3, tab_len, t, ten_cell(&x.at(), l, i, 0) / s2 + jh)? * ei(sc as i64);
        sc *= 256;
    }
    Ok(s)
}

fn xb_a(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    t: u64,
    nl: u64,
    ten: &super::attention_shape::TenAt,
    s2: u64,
    kh: u64,
) -> Result<Aff> {
    let mut s = Aff::default();
    let mut sc = 1u64;
    for l in 0..nl {
        s = s + u3_at(f, i_u3, tab_len, t, ten_cell(ten, l, 0, 0) / s2 + kh)? * ei(sc as i64);
        sc *= 256;
    }
    Ok(s)
}

/// `SA(wh, X, i, Z)`.
#[allow(clippy::too_many_arguments)]
fn sa(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    tab: &BTreeMap<String, u64>,
    y: &Lay,
    s2: u64,
    wh: &[E],
    xname: &str,
    i: u64,
    z: &str,
) -> Result<Aff> {
    let t = y.t_(xname)?;
    let tb = tab_at(tab, &format!("{}@{}", MNAME[t.mat as usize], z))?;
    let mut s = Aff::default();
    for (xh, &w) in wh.iter().enumerate() {
        s = s + long_a(f, i_u3, tab_len, tb, t, s2, i, xh as u64)? * w;
    }
    Ok(s)
}

/// `SxsA(wh, Z, sg)`.
#[allow(clippy::too_many_arguments)]
fn sxs_a(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    tab: &BTreeMap<String, u64>,
    y: &Lay,
    d: u64,
    s2: u64,
    wh: &[E],
    z: &str,
    sg: u64,
    nw_lam: u64,
) -> Result<Aff> {
    let name = if sg == 0 {
        String::from("xbI")
    } else if sg == nw_lam {
        String::from("xbO")
    } else {
        String::from("af")
    };
    let tb = tab_at(tab, &format!("{}@{}", name, z))?;
    let txs = y.t_("xs")?;
    let mut s = Aff::default();
    for xh in 0..d / s2 {
        let a = if sg == 0 || sg == nw_lam {
            xb_a(f, i_u3, tab_len, tb, y.xb.nl as u64, &y.xb, s2, xh)?
        } else {
            long_a(f, i_u3, tab_len, tb, txs, s2, sg - 1, xh)?
        };
        s = s + a * wh[xh as usize];
    }
    Ok(s)
}

/// `SBA(wh, a, b, X, i, Z, x0)`.
#[allow(clippy::too_many_arguments)]
fn sba(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    tab: &BTreeMap<String, u64>,
    y: &Lay,
    s2: u64,
    wh: &[E],
    a: u64,
    b: u64,
    xname: &str,
    i: u64,
    z: &str,
    x0: u64,
) -> Result<Aff> {
    let t = y.t_(xname)?;
    let tb = tab_at(tab, &format!("{}@{}", MNAME[t.mat as usize], z))?;
    let mut s = Aff::default();
    for xh in a / s2..b / s2 {
        s = s + long_a(f, i_u3, tab_len, tb, t, s2, i, xh - x0 / s2)? * wh[xh as usize];
    }
    Ok(s)
}

/// `shA(X, P, i, j)`.
#[allow(clippy::too_many_arguments)]
fn sh_a(
    f: &HFork,
    i_u3: u32,
    tab_len: &BTreeMap<u64, u64>,
    tab: &BTreeMap<String, u64>,
    y: &Lay,
    xname: &str,
    p: &str,
    i: u64,
    j: u64,
) -> Result<Aff> {
    let t = y.t_(xname)?;
    let tb = tab_at(tab, &format!("{}@{}", MNAME[t.mat as usize], p))?;
    short_a(f, i_u3, tab_len, tb, t, i, j)
}

/// One committed-table entry that the plan schedules (`LaterPhi`).
struct LaterPhi {
    first: usize,
    count: usize,
    point: String,
    lng: bool,
}

/// `addFun(M0, parts, L, phi, nm)` (vf_layers_check.inc:140-158).
#[allow(clippy::too_many_arguments)]
fn add_fun(
    f: &HFork,
    tl: &HTailF2,
    mats: &[super::matrices::TMat],
    m0: usize,
    parts: u64,
    l: u64,
    phi: &[E],
    nm: &str,
    p: &mut u64,
    fun: &mut Vec<HFun>,
    tab: &mut BTreeMap<String, u64>,
    tab_len: &mut BTreeMap<u64, u64>,
) -> Result<()> {
    tl.fun_open()?;
    let first = *p;
    for q in 0..parts {
        let m = &mats[m0 + q as usize];
        fun.push(HFun {
            m: (m0 as u64 + q) as i32,
            l,
            phi: phi.to_vec(),
            tree: 2,
            at: *p,
            name: format!("{}{}", f.g, nm),
        });
        *p += m.k * (m.m / l);
    }
    if *p == first {
        return Err(Refusal::internal("internal-W-length"));
    }
    tab.insert(String::from(nm), first);
    tab_len.insert(first, *p - first);
    Ok(())
}

/// `tables(mn, M0, parts, pts, lng)` (vf_layers_check.inc:177-182).
#[allow(clippy::too_many_arguments)]
fn tables(
    f: &HFork,
    tl: &HTailF2,
    mats: &[super::matrices::TMat],
    mn: &str,
    m0: usize,
    parts: u64,
    pts: &[String],
    lng: bool,
    la: u32,
    t: u64,
    later: &mut Vec<LaterPhi>,
    p: &mut u64,
    fun: &mut Vec<HFun>,
    tab: &mut BTreeMap<String, u64>,
    tab_len: &mut BTreeMap<u64, u64>,
) -> Result<()> {
    for n in pts {
        later.push(LaterPhi {
            first: fun.len(),
            count: parts as usize,
            point: n.clone(),
            lng,
        });
        add_fun(
            f,
            tl,
            mats,
            m0,
            parts,
            if lng { 1u64 << la } else { t },
            &[],
            &format!("{}@{}", mn, n),
            p,
            fun,
            tab,
            tab_len,
        )?;
    }
    Ok(())
}

/// `ewOf(sn)`: one lookup segment's key weights at zj.
fn ew_of(y: &Lay, ll: u32, sn: &str) -> Result<Vec<E>> {
    let c = call_of(y, sn)?;
    let e = eq_tab(zj(c, ll), c.l_j as usize);
    let s = c.seg(sn)?;
    let mut w = vec![E::zero(); s.n as usize];
    for x in 0..s.n as usize {
        w[x] = e[s.pos[x] as usize];
    }
    Ok(w)
}

/// `ewh(sn)`: the same, a block of S2 features at a time.
fn ewh(y: &Lay, ll: u32, ls: u32, s2: u64, sn: &str) -> Result<Vec<E>> {
    let c = call_of(y, sn)?;
    let k = cut_last(zj(c, ll), c.l_j as usize, ls as usize)?;
    let e = eq_tab(k.hi, k.nhi);
    let s = c.seg(sn)?;
    let mut w = vec![E::zero(); s.n as usize / s2 as usize];
    for xh in 0..w.len() {
        w[xh] = e[(s.pos[s2 as usize * xh] / s2) as usize];
    }
    Ok(w)
}

/// `LBU` (vf_widths_and_bounds.h:40): the lookup key of u is `u + 2^LBU`.
const LBU: u32 = 15;

/// The read-only forms of one run: the tables, the points and the stage's numbers (`LINE` and the
/// claim list read them).
struct Ctx<'a> {
    h: &'a Hdr,
    y: &'a Lay,
    kl: &'a [u32],
    g: u64,
    p3: bool,
    gcl: bool,
    rcl: bool,
    fo: &'a HForest,
    tab: &'a BTreeMap<String, u64>,
    tab_len: &'a BTreeMap<u64, u64>,
    i_u3: u32,
    t: u64,
    s2: u64,
    d: u64,
    dq: u64,
    f: u64,
    fe: u64,
    ne: u64,
    lam: u64,
    lam_m: u64,
    ll: u32,
    ls: u32,
    la: u32,
    lt: u32,
    nw: u64,
    limbs: i32,
}

impl<'a> Ctx<'a> {
    fn sh(&self, f: &HFork, x: &str, p: &str, i: u64, j: u64) -> Result<Aff> {
        sh_a(f, self.i_u3, self.tab_len, self.tab, self.y, x, p, i, j)
    }

    fn sa(&self, f: &HFork, wh: &[E], x: &str, i: u64, z: &str) -> Result<Aff> {
        sa(f, self.i_u3, self.tab_len, self.tab, self.y, self.s2, wh, x, i, z)
    }

    fn sxs(&self, f: &HFork, wh: &[E], z: &str, sg: u64) -> Result<Aff> {
        sxs_a(
            f,
            self.i_u3,
            self.tab_len,
            self.tab,
            self.y,
            self.d,
            self.s2,
            wh,
            z,
            sg,
            self.nw * self.lam,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn sba(
        &self,
        f: &HFork,
        wh: &[E],
        a: u64,
        b: u64,
        x: &str,
        i: u64,
        z: &str,
        x0: u64,
    ) -> Result<Aff> {
        sba(
            f,
            self.i_u3,
            self.tab_len,
            self.tab,
            self.y,
            self.s2,
            wh,
            a,
            b,
            x,
            i,
            z,
            x0,
        )
    }

    /// `SITE`: one lookup key's form, as in 11-2, "The keys of the lookup of step 1".
    fn site(
        &self,
        w: E,
        sq: &Aff,
        k: u32,
        form: i32,
        srh: impl FnOnce() -> Result<Aff>,
    ) -> Result<Aff> {
        let o1 = ei(128);
        let o2 = ei(32896);
        let t_of = |k: u32| if k < 16 { 16 - k } else { 0 } as u32;
        let mut v = (Aff::constant(w * pw(k - 1)) - sq.clone() * pw(k)) * pw(t_of(k));
        if form != 0 {
            let lead = if form == 1 { o1 } else { o2 };
            v = v - (Aff::constant(lead * w) + srh()?) * pw(16);
        }
        Ok(v)
    }

    /// `HIGH`: the key's high part.
    fn high(&self, w: E, srh: Aff, k: u32, form: i32) -> Aff {
        let o1 = ei(128);
        let o2 = ei(32896);
        let s = Aff::constant((if form == 1 { o1 } else { o2 }) * w) + srh;
        let top = if form == 1 { 24 } else { 32 };
        s * pw(top - if k > 16 { k } else { 16 })
    }

    fn line(&self, f: &HFork, sn: &str, lam: u64) -> Result<Aff> {
        let z = "zt";
        let l = self.g * self.lam + lam;
        let ew = ew_of(self.y, self.ll, sn)?;
        let n = ew.len() as u64;
        let w = sum_e(&ew);
        let wh: Vec<E> = if n % self.s2 == 0 && sn != "ROW" {
            ewh(self.y, self.ll, self.ls, self.s2, sn)?
        } else {
            Vec::new()
        };
        let s = |x: &str, i: u64, zz: &str| -> Result<Aff> { self.sa(f, &wh, x, i, zz) };
        let lam_m = lam / 2;
        let is_moe = self.p3 && lam % 2 == 1;
        let kq = kl(self.kl, l, LKQ) as u32;
        let kk = kl(self.kl, l, super::stage_context::LKK) as u32;
        let kv = kl(self.kl, l, super::stage_context::LKV) as u32;
        let ko = kl(self.kl, l, super::stage_context::LKO) as u32;
        let kd = kl(self.kl, l, LKD) as u32;
        let kr = if is_moe {
            kl_m(self.kl, self.h.l as u64, l, 0) as u32
        } else {
            0
        };
        let f_qk = self.h.hf[KQ_] as i32;
        let f_v = self.h.hf[KV_] as i32;
        let f_o = self.h.hf[KO_] as i32;
        let f_g = self.h.hf[KGD] as i32;
        let f_u = self.h.hf[KUD] as i32;
        let f_d = self.h.hf[KDD] as i32;
        let f_r = self.h.hf[KR_] as i32;
        let norm_k = |l: u64, first: bool| -> u32 {
            kl(self.kl, l, if first { super::stage_context::LK1 } else { super::stage_context::LK2 }) as u32
        };
        match sn {
            "G" | "U" => {
                let up = sn == "U";
                let form = if up { f_u } else { f_g };
                let qn = if up { "u" } else { "gi" };
                let rh = if up { "ru" } else { "rg" };
                let q = |a: u64, b: u64| -> Result<Aff> {
                    if up || !self.gcl {
                        self.sba(f, &wh, a, b, qn, lam, "Z", 0)
                    } else {
                        Ok(self.sba(f, &wh, a, b, "g0", lam, "Z", 0)?
                            + self.sba(f, &wh, a, b, "gh", lam, "Z", 0)? * ei(256))
                    }
                };
                if !is_moe {
                    let k = if up { self.h.hf[KUD] } else { self.h.hf[KGD] };
                    return self.site(w, &q(0, self.f)?, k, form, || s(rh, lam, "Z"));
                }
                let a = self.site(
                    sum_r(&ew, 0, self.fe),
                    &q(0, self.fe)?,
                    if up { self.h.hf[KUD] } else { self.h.hf[KGD] },
                    form,
                    || self.sba(f, &wh, 0, self.fe, rh, lam, "Z", 0),
                )?;
                let b = self.site(
                    sum_r(&ew, self.fe, self.f),
                    &q(self.fe, self.f)?,
                    kl_m(self.kl, self.h.l as u64, l, if up { 2 } else { 1 }) as u32,
                    form,
                    || self.sba(f, &wh, self.fe, self.f, rh, lam, "Z", 0),
                )?;
                Ok(a + b)
            }
            "GH" | "UH" => {
                let up = sn == "UH";
                let rh = if up { "ru" } else { "rg" };
                let form = if up { f_u } else { f_g };
                let k_full = if up { self.h.hf[KUD] } else { self.h.hf[KGD] };
                if !is_moe {
                    return Ok(self.high(w, s(rh, lam, "Z")?, k_full, form));
                }
                let a = self.high(
                    sum_r(&ew, 0, self.fe),
                    self.sba(f, &wh, 0, self.fe, rh, lam, "Z", 0)?,
                    k_full,
                    form,
                );
                let b = self.high(
                    sum_r(&ew, self.fe, self.f),
                    self.sba(f, &wh, self.fe, self.f, rh, lam, "Z", 0)?,
                    kl_m(self.kl, self.h.l as u64, l, if up { 2 } else { 1 }) as u32,
                    form,
                );
                Ok(a + b)
            }
            "UT" => Ok(s("u", lam, "Z")? + Aff::constant(pw(LBU) * w)),
            "QK" | "QKH" => {
                let mut a = Aff::default();
                for b in 0..2u64 {
                    let a0 = if b != 0 { self.dq } else { 0 };
                    let b0 = if b != 0 { self.y.nqk } else { self.dq };
                    let k = if b != 0 { kk } else { kq };
                    let wb = sum_r(&ew, a0, b0);
                    if sn == "QK" {
                        a = a
                            + self.site(wb, &self.sba(f, &wh, a0, b0, "qkw", lam, "Z", 0)?, k, f_qk, || {
                                self.sba(f, &wh, a0, b0, "rqk", lam, "Z", 0)
                            })?;
                    } else {
                        a = a + self.high(wb, self.sba(f, &wh, a0, b0, "rqk", lam, "Z", 0)?, k, f_qk);
                    }
                }
                Ok(a)
            }
            "N1" | "N2" => {
                let n1 = sn == "N1";
                self.site(w, &s(if n1 { "aw" } else { "mw" }, lam, "Z")?, norm_k(l, n1), 2, || {
                    s(if n1 { "ra" } else { "rm" }, lam, "Z")
                })
            }
            "N1H" | "N2H" => {
                let n1 = sn == "N1H";
                Ok(self.high(w, s(if n1 { "ra" } else { "rm" }, lam, "Z")?, norm_k(l, n1), 2))
            }
            "O" => {
                let q = self.sxs(f, &wh, "Z", 2 * lam + 1)? - self.sxs(f, &wh, "Z", 2 * lam)?;
                self.site(w, &q, ko, f_o, || s("ro", lam, "Z"))
            }
            "D" => {
                let q = self.sxs(f, &wh, "Z", 2 * lam + 2)? - self.sxs(f, &wh, "Z", 2 * lam + 1)?;
                self.site(w, &q, kd, f_d, || s("rd", lam, "Z"))
            }
            "V" => self.site(w, &s("vw", lam, "Z")?, kv, f_v, || s("rv", lam, "Z")),
            "OH" => Ok(self.high(w, s("ro", lam, "Z")?, ko, f_o)),
            "DH" => Ok(self.high(w, s("rd", lam, "Z")?, kd, f_d)),
            "VH" => Ok(self.high(w, s("rv", lam, "Z")?, kv, f_v)),
            "ROW" => {
                let trow = self.y.t_("row")?;
                let t = tab_at(self.tab, &format!("ar@{}", z))?;
                let nrl = led_nr(self.limbs) as u64;
                let mut a = Aff::default();
                for x in 0..n as usize {
                    let np = x as u64 / nrl;
                    let idx = x as u64 % nrl;
                    let mu = led_mu(idx as i32, self.limbs);
                    let cell = u3_at(
                        f,
                        self.i_u3,
                        self.tab_len,
                        t,
                        trow.off + (self.y.nn * lam + np) * nrl + idx,
                    )? + Aff::constant(ei(128));
                    a = a + cell * e_scale(ew[x], mu);
                }
                Ok(a)
            }
            "CN1" | "CN2" => {
                let mut b = Aff::default();
                for x in 0..self.d {
                    b = b + self.sh(f, if sn == "CN1" { "a" } else { "m" }, z, lam, x)? * ew[x as usize];
                }
                Ok(s(if sn == "CN1" { "aw" } else { "mw" }, lam, "Z")?
                    + b * pw(28)
                    + Aff::constant(w * ei((1i64 << 15) + (1i64 << 39))))
            }
            "CQK" => Ok(s("qkw", lam, "Z")?
                + (self.sba(f, &wh, 0, self.dq, "q", lam, "Z", 0)?
                    + self.sba(f, &wh, self.dq, self.y.nqk, "kx", lam, "Z", self.dq)?)
                    * pw(28)
                + Aff::constant(w * ei((1i64 << 15) + (1i64 << 39)))),
            "CV" => Ok(s("vw", lam, "Z")?
                + s("v", lam, "Z")? * pw(28)
                + Aff::constant(w * ei((1i64 << 15) + (1i64 << 39)))),
            "F" => {
                let base = if self.gcl {
                    s("g0", lam, "Z")? + s("gc", lam, "Z")? * ei(256)
                } else {
                    s("gi", lam, "Z")?
                };
                Ok(base
                    + s("s", lam, "Z")? * pw(28)
                    + Aff::constant(w * ei((1i64 << 15) + (1i64 << 40))))
            }
            "G0" => Ok(s("g0", lam, "Z")? + Aff::constant(w * ei(128))),
            "CG" => Ok(s("gh", lam, "Z")?
                + s("gc", lam, "Z")? * pw(28)
                + Aff::constant(w * ei(49152 + (1i64 << 35) + (1i64 << 40)))),
            "XR" => {
                let mut b = Aff::default();
                for x in 0..self.d {
                    b = b + self.sh(f, "xr", z, lam_m, x)? * ew[x as usize];
                }
                Ok(Aff::constant(pw(15) * w) - b * pw(16))
            }
            "LR" => {
                let mut q = Aff::default();
                for x in 0..self.ne {
                    let cell = if self.rcl {
                        self.sh(f, "ly", z, lam_m, x)? * ei(8) + self.sh(f, "l3", z, lam_m, x)?
                    } else {
                        self.sh(f, "lr", z, lam_m, x)?
                    };
                    q = q + cell * ew[x as usize];
                }
                let srh = || {
                    let mut s = Aff::default();
                    for x in 0..self.ne {
                        s = s + self.sh(f, "rl", z, lam_m, x)? * ew[x as usize];
                    }
                    Ok(s)
                };
                self.site(w, &q, kr, f_r, srh)
            }
            "LT" => {
                let mut a = Aff::default();
                for x in 0..self.ne {
                    a = a + (self.sh(f, "lr", z, lam_m, x)? + Aff::constant(pw(14))) * e_scale(ew[x as usize], 2);
                }
                Ok(a)
            }
            "DD" => {
                let mut a = Aff::default();
                let mut tail = Aff::default();
                for x in (0..self.ne).rev() {
                    a = a + (self.sh(f, "lr", z, lam_m, x)? + tail.clone()) * (E::zero() - ew[x as usize]);
                    tail = tail + self.sh(f, "sel", z, lam_m, x)?;
                }
                Ok(a)
            }
            "LH" => {
                let mut s = Aff::default();
                for x in 0..self.ne {
                    s = s + self.sh(f, "rl", z, lam_m, x)? * ew[x as usize];
                }
                Ok(self.high(w, s, kr, f_r))
            }
            "SEL" => {
                let mut a = Aff::default();
                for x in 0..self.ne {
                    a = a + self.sh(f, "sel", z, lam_m, x)? * e_scale(ew[x as usize], 128);
                }
                Ok(a)
            }
            "MR" => Ok((Aff::constant(pw(if self.gcl { 14 } else { 15 }))
                + self.sh(f, "sc", z, lam_m, 0)? * pw(17))
                * ew[0]),
            "L3" => {
                let mut a = Aff::default();
                for x in 0..self.ne {
                    a = a + self.sh(f, "l3", z, lam_m, x)? * e_scale(ew[x as usize], 32);
                }
                Ok(a)
            }
            "CLR" => {
                let mut a = Aff::default();
                for x in 0..self.ne {
                    a = a
                        + (self.sh(f, "ly", z, lam_m, x)?
                            + (self.sh(f, "lr", z, lam_m, x)? - self.sh(f, "l3", z, lam_m, x)?) * pw(25))
                            * ew[x as usize];
                }
                Ok(a + Aff::constant(w * ei((1i64 << 15) + (1i64 << 39))))
            }
            _ => Err(Refusal::named(&format!("hid-profile-segment-{}", sn))),
        }
    }
}

/// `runForkHidG2(g)` (vf_layers_check.inc:26-1204): one layer group's whole check. The result is
/// the sub-proof's record of its weight claims and the counts the caller logs.
pub fn run_layer_g(
    inp: &LayerCheckInputs<'_>,
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    gate: &mut dyn AttentionSegment,
    calls: &mut HashCalls,
) -> Result<LayerRunOut> {
    let h = inp.h;
    let y = inp.y;
    let hp = inp.plan;
    let g = inp.g;
    let p3 = inp.p3;
    let la = h.la;
    let lt = h.lt;
    let ll = h.ll;
    let ls = y.ls as u32;
    let s2 = y.s2;
    let d = h.d;
    let dq = y.dq;
    let t = y.t;
    let lam = y.lam;
    let lam_m = y.lam_m;
    let ne = h.ne;
    let nw = y.nw;
    let ni = y.ni;
    let nn = y.nn;
    let ldh = y.ldh as u32;
    let l_pd = y.l_pd;
    let l_pf = y.l_pf;
    let lfe = y.lfe;
    let ds2 = d / s2;
    let nsl = led_ns(inp.limbs);
    let npl = led_np(inp.limbs);
    let nrl = led_nr(inp.limbs);
    let no_l = led_no(inp.limbs);
    f.g = format!("G{}:", g);
    f.trees = hp.fp.trees.clone();
    fill_l(f);
    let mut tl = hp.tl.clone();
    let mut t2 = hp.tp.clone();
    let i_u3 = tl.ix.u[2] as u32;
    let mut yy = y.clone();
    super::stage_layout::set_tau(&mut yy, y);
    f.slots(hp.ns);
    let mut slot = 0u32;
    // Step 1: one lookup (`forest`) for all calls.
    let cl1: Vec<super::common::Call> = yy.calls.iter().map(|c| c.c.clone()).collect();
    let mut fo = forest_pad(f, tr, &cl1, &y.fo.pub_, &mut slot, inp.lidb, calls)?;
    for q in 0..yy.calls.len() {
        yy.calls[q].c.alpha = fo.alpha;
        yy.calls[q].c.zk = fo.zk[q].clone();
    }
    let nc = yy.calls.len();
    if fo.d_t != y.fo.d_t
        || fo.k_t != y.fo.k_t
        || fo.nt != y.fo.nt
        || fo.r_k != y.fo.r_k
        || fo.first != y.fo.first
        || fo.iota != y.fo.iota
        || fo.call_of != y.fo.call_of
    {
        return Err(Refusal::internal(&format!("{}internal-g-forest", f.g)));
    }
    // Step 2: P_V, the norms' token point. Step 3, group 0 only: the embedding's points.
    let pv = tr_point(tr, RoundName::Zero, lt as usize, calls)?;
    let has_e = g == 0;
    let (ze, tkh) = if has_e {
        (
            tr_point(tr, RoundName::Zero, (ls + lt) as usize, calls)?,
            tr_point(tr, RoundName::Zero, (l_pd - ls as i32) as usize, calls)?,
        )
    } else {
        (Vec::new(), Vec::new())
    };
    if (fo.d_t as u32) < la {
        return Err(Refusal::named("forest-depth-G"));
    }
    for c in &yy.calls {
        for i in 0..la as usize {
            let zk = &c.c.zk;
            if zk[zk.len() - la as usize + i] != fo.zx[fo.d_t as usize - la as usize + i] {
                return Err(Refusal::internal(&format!("{}internal-g-merged-point", f.g)));
            }
        }
    }
    let zt_f: Vec<E> = fo.zx[fo.zx.len() - lt as usize..].to_vec();
    let _ = dq;
    // The lookup call list of this file's planning (`y.fo`): one call per entry.
    let mut pt: BTreeMap<String, Vec<E>> = BTreeMap::new();
    pt.insert(String::from("Z"), last_of(&fo.zx, la as usize)?);
    pt.insert(String::from("zt"), zt_f.clone());
    if has_e {
        pt.insert(String::from("Z_E"), ze.clone());
    }
    // The evaluation tables (U3) and their offsets.
    let i_ad = y.parts[0] as usize;
    let i_ar = i_ad + y.parts[1] as usize;
    let i_b = i_ar + 1;
    let i_qa = i_b + 1;
    let i_xo = i_qa + 1;
    let i_xi = i_xo + 1;
    let mut fun: Vec<HFun> = Vec::new();
    let mut tab: BTreeMap<String, u64> = BTreeMap::new();
    let mut tab_len: BTreeMap<u64, u64> = BTreeMap::new();
    let mut later_phi: Vec<LaterPhi> = Vec::new();
    let mut p = 0u64;
    let mats = &hp.tl.mats;
    tables(f, &tl, mats, "af", 0, y.parts[0], &inp.reads.af, true, la, t, &mut later_phi, &mut p, &mut fun, &mut tab, &mut tab_len)?;
    tables(f, &tl, mats, "qa", i_qa, 1, &inp.reads.qa, true, la, t, &mut later_phi, &mut p, &mut fun, &mut tab, &mut tab_len)?;
    tables(f, &tl, mats, "xbI", i_xi, 1, &inp.reads.xi, true, la, t, &mut later_phi, &mut p, &mut fun, &mut tab, &mut tab_len)?;
    if has_e {
        tables(f, &tl, mats, "xbI", i_xi, 1, &[String::from("Z_E")], true, la, t, &mut later_phi, &mut p, &mut fun, &mut tab, &mut tab_len)?;
    }
    tables(f, &tl, mats, "xbO", i_xo, 1, &inp.reads.xo, true, la, t, &mut later_phi, &mut p, &mut fun, &mut tab, &mut tab_len)?;
    tables(f, &tl, mats, "ad", i_ad, y.parts[1], &inp.reads.ad, false, la, t, &mut later_phi, &mut p, &mut fun, &mut tab, &mut tab_len)?;
    tables(f, &tl, mats, "ar", i_ar, 1, &inp.reads.ar, false, la, t, &mut later_phi, &mut p, &mut fun, &mut tab, &mut tab_len)?;
    tables(f, &tl, mats, "qa", i_qa, 1, &inp.reads.qs, false, la, t, &mut later_phi, &mut p, &mut fun, &mut tab, &mut tab_len)?;
    let trow = y.t_("row")?.clone();
    let mb = 1u64 << h.lmb;
    for e in 0..2usize {
        add_fun(
            f,
            &tl,
            mats,
            i_b,
            1,
            mb,
            &super::lookup::forest_phi_b(&fo, h.lmb as i32, e)?,
            if e == 1 { "b-bits-1" } else { "b-bits-0" },
            &mut p,
            &mut fun,
            &mut tab,
            &mut tab_len,
        )?;
    }
    add_fun(f, &tl, mats, i_b, 1, mb, &super::lookup::forest_phi_p(h.lmb as i32), "b-pin", &mut p, &mut fun, &mut tab, &mut tab_len)?;
    if p != hp.n_u[2] {
        return Err(Refusal::internal("internal-W-length"));
    }
    // The QK call's weights AH and lfc.
    let mut ah: Vec<E> = vec![E::zero(); 64];
    let mut lfc: Vec<E> = Vec::new();
    {
        let c = call_of(&yy, "QK")?;
        let k = cut_last(zj(c, ll), c.l_j as usize, ldh as usize)?;
        let e = eq_tab(k.hi, k.nhi);
        let s = c.seg("QK")?;
        let tq = y.t_("q")?.at();
        let tk = y.t_("kx")?.at();
        for hd_ in 0..(h.h + h.gk) {
            let pos = if hd_ < h.h {
                head_feat(&tq, hd_, h.dh)?
            } else {
                tq.j + head_feat(&tk, hd_ - h.h, h.dh)?
            };
            ah[hd_ as usize] = e[s.pos[pos as usize] as usize / h.dh as usize];
        }
        lfc = eq_tab(k.lo, ldh as usize);
    }
    // Step 8: TSC(P_V). Step 9: TSC(zt), unless the call list has no terms.
    let nsl_i = nsl as u64;
    let s_w = f.claims_in(tr, &mut slot, (nsl_i * ni) as u32)?;
    let gp = tr_batch(tr, nsl as usize, calls)?;
    let l_ni = l_ni_usize(y.ni);
    let rho_i = if l_ni != 0 { tr_point(tr, RoundName::Join, l_ni, calls)? } else { Vec::new() };
    let wpl = {
        let e = eq_tab(&rho_i, l_ni_usize(y.ni));
        let half = ei(2).inv();
        let mut scale = E::one();
        for _ in 0..l_pd {
            scale = scale * half;
        }
        let mut c = Aff::default();
        for i in 0..ni {
            let w = scale * e[i as usize];
            for s in 0..nsl_i {
                c = c + Aff::slot(s_w + (nsl_i * i + s) as u32) * (w * gp[s as usize]);
            }
        }
        let mut rho = rho_i.clone();
        for _ in 0..l_pd {
            rho.push(half);
        }
        rho.extend_from_slice(&pv);
        read_product_level_rounds(
            f,
            tr,
            &mut slot,
            mu_v_usize(inp),
            &rho,
            &c,
            &order_default(mu_v_usize(inp)),
            calls,
        )?
    };
    pt.insert(String::from("Z_V"), last_of(&wpl.r, la as usize)?);
    let s_pv = f.claims_in(tr, &mut slot, (npl as u64 * ni) as u32)?;
    let om_v = tr_batch(tr, (npl as u64 * ni) as usize, calls)?;
    let has_t = !inp.reads.tsc_calls.is_empty();
    let is_moe = |l: u64| p3 && l % 2 == 1;
    let no_ol = no_l as u64;
    let mut t_v = tsc_in(f, tr, &mut slot, &pv, lt as i32, (no_ol * ni) as u32, 2, calls)?;
    pt.insert(String::from("P_V"), pv.clone());
    pt.insert(String::from("r_tV"), t_v.r.clone());
    let mut s_sc = 0u32;
    let mut s_sel = 0u32;
    let mut kt = Aff::default();
    let mut t_t: Option<TokenSumcheckState> = None;
    let n_end_t = nn * lam + if p3 { lam_m * (1 + ne) } else { 0 };
    if has_t {
        let mut tt = tsc_in(
            f,
            tr,
            &mut slot,
            &zt_f,
            lt as i32,
            n_end_t as u32,
            1,
            calls,
        )?;
        s_sc = tt.s_end + (nn * lam) as u32;
        s_sel = s_sc + lam_m as u32;
        pt.insert(
            String::from("Y"),
            long_point(&fo.zx[fo.d_t as usize - la as usize..], ls as usize, &tt.r),
        );
        pt.insert(String::from("rt"), tt.r.clone());
        if tt.p.eps == E::zero() {
            return Err(Refusal::named("coin-zero"));
        }
        kt = psc_row(f, &mut tt.p, E::zero(), &Aff::default())? * (E::zero() - tt.p.eps.inv());
        t_t = Some(tt);
    }
    let mut ctx = Ctx {
        h,
        y: &yy,
        kl: inp.kl,
        g,
        p3,
        gcl: inp.gcl != 0,
        rcl: inp.rcl != 0,
        fo: &fo,
        tab: &tab,
        tab_len: &tab_len,
        i_u3,
        t,
        s2,
        d,
        dq,
        f: h.f,
        fe: h.fe,
        ne,
        lam,
        lam_m,
        ll,
        ls,
        la,
        lt,
        nw,
        limbs: inp.limbs,
    };
    // om[0] = 1 for the join; om[1], a challenge, for KT, only if tscCalls is not empty.
    let om = if has_t {
        tr_batch(tr, 2, calls)?
    } else {
        vec![E::one()]
    };
    // ---- JF, the join, and the batched sumcheck's start form ----
    let mut laid = vec![0u64; fo.nt as usize];
    let mut cstart = Aff::default();
    for q in 0..nc {
        let jp = join_part(&ctx, f, &yy, q, &mut laid, has_t)?;
        cstart = cstart + jp * fo.e[q];
    }
    {
        let ey = eq_tab(&fo.zy, fo.r_k as usize);
        for t_ in fo.nt as usize..(1usize << fo.r_k) {
            cstart = cstart + Aff::constant(ey[t_] * (fo.alpha - fo.pad_key(0)));
        }
    }
    if has_t {
        cstart = cstart - Aff::slot(t_t.as_ref().unwrap().s_cl);
    }
    cstart = cstart - fo.c_end.clone();
    if has_t {
        cstart = cstart + kt * om[1];
    }
    let mut st = super::lookup::HStack { lam: hp.lam_s, rs: Vec::new(), p: Default::default() };
    st.p = psc_begin(f, tr, &mut slot, &cstart, calls)?;
    super::lookup::stack_rounds(f, tr, &mut slot, &mut st, calls)?;
    // ---- The panels ----
    let mut bl: Vec<Panel> = Vec::new();
    let mut next_v: i64 = 0;
    let mut ac: Vec<usize> = Vec::new();
    for (q, c) in yy.calls.iter().enumerate() {
        if c.segs.iter().any(|s| is_acc(&s.name)) {
            ac.push(q);
        }
    }
    let mut ts: Vec<usize> = Vec::new();
    for n in &inp.reads.tsc_calls {
        ts.push(call_no(&yy, n)?);
    }
    let le = ceil_log2(if ne != 0 { ne } else { 1 }) as u32;
    let t_of = |k: u32| if k < 16 { 16 - k } else { 0 };
    let k_t = |l: u64, i: usize| pw(t_of(kl(inp.kl, l, i)));
    let k_tm = |l: u64, i: usize| pw(t_of(kl_m(inp.kl, h.l as u64, l, i)));
    let lay = |lam: u64| g * lam + lam;
    let mut ec_now = E::zero();
    // Plain panels: A and B precomputed, `None` for the weights side.
    for ci in 0..ac.len() {
        let c = &yy.calls[ac[ci]];
        let _el = eq_tab(zl(c), ll as usize);
        ec_now = fo.e[ac[ci]];
        for s in &c.segs {
            let sn = s.name.as_str();
            if sn == "G" || sn == "U" {
                let up = sn == "U";
                let mut a = Vec::new();
                for i in 0..ctx.lam {
                    for k2 in 0..ctx.d {
                        a.push(ctx.sh(f, "m", "zt", i, k2) ?);
                    }
                }
                let mut wt = Vec::new();
                for i in 0..ctx.lam {
                    wt.push(_el[i as usize] * k_t(lay(i), if up { super::stage_context::LKU } else { LKG }));
                }
                push_panel(&mut bl, 0, ec_now, ctx.lam, ctx.d, a, None, wt, &mut next_v);
            } else if sn == "V" {
                let mut a = Vec::new();
                for i in 0..ctx.lam {
                    for k2 in 0..ctx.d {
                        a.push(ctx.sh(f, "a", "zt", i, k2) ?);
                    }
                }
                let mut wt = Vec::new();
                for i in 0..ctx.lam {
                    wt.push(_el[i as usize] * k_t(lay(i), super::stage_context::LKV));
                }
                push_panel(&mut bl, 0, ec_now, ctx.lam, ctx.d, a, None, wt, &mut next_v);
            } else if sn == "O" {
                let mut a = Vec::new();
                for i in 0..ctx.lam {
                    for k2 in 0..ctx.dq {
                        a.push(ctx.sh(f, "o", "zt", i, k2) ?);
                    }
                }
                let mut wt = Vec::new();
                for i in 0..ctx.lam {
                    wt.push(_el[i as usize] * k_t(lay(i), super::stage_context::LKO));
                }
                push_panel(&mut bl, 0, ec_now, ctx.lam, ctx.dq, a, None, wt, &mut next_v);
            } else if sn == "D" {
                let mut wt = Vec::new();
                for i in 0..ctx.lam {
                    wt.push(_el[i as usize] * k_t(lay(i), LKD));
                }
                push_panel(&mut bl, 0, ec_now, ctx.lam, ctx.f, Vec::new(), None, wt, &mut next_v);
                bl.last_mut().unwrap().virt = 0;
            } else if sn == "LR" {
                let mut a = Vec::new();
                for i in 0..ctx.lam_m {
                    for k2 in 0..ctx.d {
                        a.push(ctx.sh(f, "m", "zt", 2 * i + 1, k2) ?);
                    }
                }
                let mut wt = Vec::new();
                for i in 0..ctx.lam_m {
                    wt.push(_el[(2 * i + 1) as usize] * k_tm(lay(2 * i + 1), 0));
                }
                push_panel(&mut bl, 0, ec_now, ctx.lam_m, ctx.d, a, None, wt, &mut next_v);
            }
        }
    }
    for ti in 0..ts.len() {
        if ts[ti] == usize::MAX {
            continue;
        }
        let c = &yy.calls[ts[ti]];
        let el = eq_tab(zl(c), ll as usize);
        ec_now = fo.e[ts[ti]];
        for s in &c.segs {
            let sn = s.name.as_str();
            if sn == "N1" || sn == "N2" {
                let n2 = if sn == "N2" { 1 } else { 0 };
                let wh = ewh(&yy, ll, ls, s2, sn)?;
                let mut a = vec![Aff::default(); ctx.lam as usize];
                let mut b = vec![Aff::default(); ctx.lam as usize];
                for i in 0..ctx.lam {
                    a[i as usize] = Aff::constant(f.shown(
                        t_t.as_ref().unwrap().s_end + (2 * i + n2) as u32,
                    )?);
                    b[i as usize] = ctx.sxs(f, &wh, "Y", 2 * i + n2)?;
                }
                let wt: Vec<E> = (0..ctx.lam).map(|i| el[i as usize]).collect();
                push_panel(&mut bl, 1, ec_now, ctx.lam, 1, a, Some(b), wt, &mut next_v);
            } else if sn == "QK" {
                let mut a = Vec::new();
                for i in 0..ctx.lam {
                    for k2 in 0..ctx.d {
                        a.push(ctx.sh(f, "a", "rt", i, k2) ?);
                    }
                }
                let mut wt = Vec::new();
                for i in 0..ctx.lam {
                    wt.push(el[i as usize] * k_t(lay(i), LKQ));
                }
                push_panel(&mut bl, 1, ec_now, ctx.lam, ctx.d, a, None, wt, &mut next_v);
            } else if !p3 {
                continue;
            } else if sn == "XR" {
                let ew = ew_of(&yy, ll, "XR")?;
                let mut a = vec![Aff::default(); ctx.lam_m as usize];
                let mut b = vec![Aff::default(); ctx.lam_m as usize];
                for i in 0..ctx.lam_m {
                    let lam = 2 * i + 1;
                    a[i as usize] = Aff::constant(f.shown(s_sc + (lam / 2) as u32)?);
                    let mut bb = Aff::default();
                    for x in 0..ctx.d {
                        bb = bb + ctx.sh(f, "m", "rt", lam, x)? * ew[x as usize];
                    }
                    b[i as usize] = bb;
                }
                let wt: Vec<E> = (0..ctx.lam_m).map(|i| el[(2 * i + 1) as usize]).collect();
                push_panel(&mut bl, 1, ec_now, ctx.lam_m, 1, a, Some(b), wt, &mut next_v);
            } else if sn == "DD" || sn == "MR" {
                let ew = ew_of(&yy, ll, sn)?;
                let ws = if sn == "DD" { sum_e(&ew) } else { ew[0] };
                let mut a = Vec::new();
                let mut b = Vec::new();
                for i in 0..ctx.lam_m {
                    let lam = 2 * i + 1;
                    for e in 0..ne {
                        a.push(Aff::constant(f.shown(
                            s_sel + ((lam / 2) * ne + e) as u32,
                        )?));
                        b.push(ctx.sh(f, "lr", "rt", lam / 2, e)?);
                    }
                }
                let wt: Vec<E> = (0..ctx.lam_m)
                    .map(|i| el[(2 * i + 1) as usize] * ws)
                    .collect();
                push_panel(&mut bl, 1, ec_now, ctx.lam_m, ne, a, Some(b), wt, &mut next_v);
            } else if sn == "G" || sn == "U" || sn == "D" {
                for lm in 0..ctx.lam_m {
                    let lam = 2 * lm + 1;
                    let mut sl = Vec::new();
                    for e in 0..ne {
                        sl.push(f.shown(s_sel + (lm * ne + e) as u32)?);
                    }
                    let mut xx = Vec::new();
                    let mut virt = -1i64;
                    let wt = if sn == "D" {
                        virt = 1 + lm as i64;
                        el[lam as usize] * k_t(lay(lam), LKD)
                    } else {
                        let up = sn == "U";
                        for k2 in 0..ctx.d {
                            xx.push(ctx.sh(f, "xr", "rt", lm, k2)?);
                        }
                        el[lam as usize] * k_tm(lay(lam), if up { 2 } else { 1 })
                    };
                    push_tri(
                        &mut bl,
                        1,
                        ec_now,
                        ne,
                        if sn == "D" { ctx.fe } else { ctx.d },
                        sl,
                        xx,
                        virt,
                        wt,
                        le,
                        &mut next_v,
                    );
                }
            }
        }
    }
    // Shift the panels: largest first, so each is aligned; ties in list order.
    {
        let mut ord: Vec<usize> = (0..bl.len()).collect();
        ord.sort_by(|&a, &b| bl[b].w.cmp(&bl[a].w));
        let mut off = 0u64;
        for i in ord {
            bl[i].off = off;
            off += 1u64 << bl[i].w;
        }
        if ceil_log2(off) as i32 != hp.lam_s {
            return Err(Refusal::internal(&format!("{}internal-stack", f.g)));
        }
    }
    // ---- The end values and the batch's row ----
    let nvirt = 1 + if p3 { lam_m } else { 0 };
    let nclp = hp.n_cl as u64 - if has_e { 1 } else { 0 };
    if next_v as u64 != nclp {
        return Err(Refusal::internal(&format!("{}internal-claim-count", f.g)));
    }
    let s_a0 = psc_ends(f, tr, &mut slot, &mut st.p, 2, (2 + nvirt + nclp) as u32, calls)?;
    let s_h1 = s_a0 + 1;
    let s_b0 = s_h1 + nvirt as u32;
    let s_v = s_b0 + 1;
    let mut a_lin = Aff::default();
    let mut b_lin = Aff::default();
    let mut w_d = 0u32;
    let mut as_ = f.shown(s_a0)?;
    let mut bs = f.shown(s_b0)?;
    for pn in &bl {
        let sb = eq_low_at(&st.rs, pn.w as i32, st.lam, pn.off >> pn.w)?;
        let ey = eq_low(&st.rs, 0, pn.wy as i32);
        let ei = eq_low(&st.rs, pn.wy as i32, pn.w as i32);
        let co = sb * om[pn.claim] * pn.ec;
        if pn.tri {
            let mut s1 = E::zero();
            for e in 0..ne {
                s1 = s1 + pn.sl[e as usize] * ei[e as usize];
            }
            if pn.virt >= 0 {
                if pn.wy != lfe as u32 {
                    return Err(Refusal::internal(&format!("{}internal-stack", f.g)));
                }
                as_ = as_ + co * pn.wt[0] * s1 * f.shown(s_h1 + pn.virt as u32)?;
            } else {
                for k2 in 0..pn.ny {
                    a_lin = a_lin
                        + pn.xx[k2 as usize].clone()
                            * (co * pn.wt[0] * s1 * ey[k2 as usize]);
                }
            }
            bs = bs + sb * f.shown(s_v + pn.v0 as u32)?;
            continue;
        }
        if pn.virt >= 0 {
            if pn.v0 < 0 || w_d != 0 {
                return Err(Refusal::internal(&format!("{}internal-stack", f.g)));
            }
            w_d = pn.w;
            as_ = as_ + sb * om[pn.claim] * f.shown(s_h1 + pn.virt as u32)?;
            for i in 0..pn.ni {
                bs = bs
                    + sb * ei[i as usize]
                        * (pn.ec * pn.wt[i as usize] * f.shown(s_v + pn.v0 as u32 + i as u32)?);
            }
            continue;
        }
        for i in 0..pn.ni {
            for yv in 0..pn.ny {
                let idx = (i * pn.ny + yv) as usize;
                a_lin = a_lin + pn.a[idx].clone() * (co * pn.wt[i as usize] * ei[i as usize] * ey[yv as usize]);
                if pn.v0 < 0 {
                    b_lin = b_lin + pn.b[idx].clone() * (sb * ei[i as usize] * ey[yv as usize]);
                }
            }
            if pn.v0 >= 0 {
                bs = bs + sb * ei[i as usize] * f.shown(s_v + pn.v0 as u32 + i as u32)?;
            }
        }
    }
    if w_d != (ll + l_pf as u32) {
        return Err(Refusal::internal(&format!("{}internal-stack", f.g)));
    }
    let row_s = psc_row(f, &mut st.p, as_ * bs, &Aff::default())?;
    // ---- The product layer for hh = s u ----
    let mu_h = (ll as i32 + l_pf + lt as i32) as usize;
    let mu_h2 = (ll as i32 - 1 + lfe + lt as i32) as usize;
    let hd = {
        let mut rho = Vec::new();
        for v in (0..w_d as usize).rev() {
            rho.push(st.rs[v]);
        }
        rho.extend_from_slice(&zt_f);
        read_product_level_rounds(f, tr, &mut slot, mu_h, &rho, &Aff::slot(s_h1), &order_range(mu_h), calls)?
    };
    pt.insert(String::from("Z_a"), last_of(&hd.r, la as usize)?);
    let mut hd2: Option<ProductLevel> = None;
    if p3 {
        if !has_t {
            return Err(Refusal::internal(&format!("{}internal-g-routed-without-terms", f.g)));
        }
        let mut rho = if ll > 1 {
            tr_point(tr, RoundName::Join, (ll - 1) as usize, calls)?
        } else {
            Vec::new()
        };
        let e = eq_tab(&rho, (ll - 1) as usize);
        let mut c = Aff::default();
        for lm in 0..lam_m {
            c = c + Aff::slot(s_h1 + 1 + lm as u32) * e[lm as usize];
        }
        let tt = t_t.as_ref().unwrap();
        for v in (0..lfe as usize).rev() {
            rho.push(st.rs[v]);
        }
        rho.extend_from_slice(&tt.r);
        let h = read_product_level_rounds(f, tr, &mut slot, mu_h2, &rho, &c, &order_range(mu_h2), calls)?;
        pt.insert(String::from("Z_b"), last_of(&h.r, la as usize)?);
        hd2 = Some(h);
    }
    // ---- The weight claims ----
    let mut ui_of: BTreeMap<(u32, u32), u32> = BTreeMap::new();
    for (i, u) in inp.ws_lay.u.iter().enumerate() {
        ui_of.insert((u.x, u.l), i as u32);
    }
    let le_ = ceil_log2(if ne != 0 { ne } else { 1 }) as i32;
    let fac_rs = |st: &super::lookup::HStack, g: &super::weights_layout::WsGrp, lo0: i32, wtot: i32| -> WsFac {
        let mut x = WsFac::default();
        for i in 0..g.z {
            x.pt.push(st.rs[(lo0 + g.z - 1 - i) as usize]);
        }
        let e = eq_low(&st.rs, lo0 + g.z, lo0 + wtot);
        for hi in 0..g.o {
            x.hv.push(e[hi as usize]);
        }
        x
    };
    let fac_ew = |g: &super::weights_layout::WsGrp, sn: &str, x0: u64| -> Result<WsFac> {
        let c = call_of(&yy, sn)?;
        let s = c.seg(sn)?;
        let mut x = WsFac::default();
        for i in 0..g.z {
            x.pt.push(zj(c, ll)[c.l_j as usize - g.z as usize + i as usize]);
        }
        let e = eq_tab(zj(c, ll), (c.l_j - g.z) as usize);
        for xh in 0..g.o {
            x.hv.push(e[(s.pos[(x0 + (xh << g.z)) as usize] >> g.z) as usize]);
        }
        Ok(x)
    };
    let mut claims: Vec<WsClaim> = Vec::new();
    let mut claim = |x_: u32, lam_in: u64, fac: &mut dyn FnMut(&super::weights_layout::WsGrp) -> Result<WsFac>| -> Result<()> {
        let ui = match ui_of.get(&(x_, (g * lam + lam_in) as u32)) {
            Some(&u) => u,
            None => return Err(Refusal::internal(&format!("{}internal-claim-unit", f.g))),
        };
        let mut c = WsClaim { ui, f: Vec::new() };
        for gg in &inp.ws_lay.u[ui as usize].g {
            c.f.push(fac(gg)?);
        }
        claims.push(c);
        Ok(())
    };
    for ci in 0..ac.len() {
        let c = &yy.calls[ac[ci]];
        for s in &c.segs {
            let sn = s.name.as_str();
            if !is_acc(sn) {
                continue;
            }
            let cnt = if sn == "LR" { lam_m } else { lam };
            for i in 0..cnt {
                let lam = if sn == "LR" { 2 * i + 1 } else { i };
                let mo = is_moe(lam);
                let x_ = match sn {
                    "G" => {
                        if mo { 5 } else { 3 }
                    }
                    "U" => {
                        if mo { 6 } else { 4 }
                    }
                    "V" => 1,
                    "O" => 2,
                    "D" => 9,
                    _ => 11,
                };
                let wy = ceil_log2(if sn == "O" {
                    dq
                } else if sn == "D" {
                    h.f
                } else {
                    d
                }) as i32;
                let mut fac = |gg: &super::weights_layout::WsGrp| -> Result<WsFac> {
                    if gg.name == "kk" {
                        Ok(fac_rs(&st, gg, 0, wy))
                    } else {
                        fac_ew(gg, sn, 0)
                    }
                };
                claim(x_, lam, &mut fac)?;
            }
        }
    }
    for ti in 0..ts.len() {
        let c = &yy.calls[ts[ti]];
        for s in &c.segs {
            let sn = s.name.as_str();
            if sn == "QK" {
                let tt = t_t.as_ref().unwrap();
                let et = eq_tab(&tt.r, lt as usize);
                for lm in 0..lam {
                    let mut kap = vec![E::zero(); h.dh as usize];
                    // `l = g * Lam + lam`, with `Lam` the shape's and `lam` this layer index.
                    let l = g * lam + lm;
                    for i in 0..h.dh / 2 {
                        let mut ct = E::zero();
                        let mut st_ = E::zero();
                        for tq in 0..t {
                            let cv = rope_c(h, inp.kl, l, tq, i, false);
                            let sv = rope_c(h, inp.kl, l, tq, i, true);
                            if cv != 0 {
                                ct = ct + e_scale(et[tq as usize], fint(cv));
                            }
                            if sv != 0 {
                                st_ = st_ + e_scale(et[tq as usize], fint(sv));
                            }
                        }
                        kap[(2 * i) as usize] = ct * lfc[(2 * i) as usize] + st_ * lfc[(2 * i + 1) as usize];
                        kap[(2 * i + 1) as usize] =
                            ct * lfc[(2 * i + 1) as usize] - st_ * lfc[(2 * i) as usize];
                    }
                    let mut fac = |gg: &super::weights_layout::WsGrp| -> Result<WsFac> {
                        let mut x = WsFac::default();
                        if gg.name == "hd" {
                            x.av = ah.clone();
                        } else if gg.name == "cd" {
                            x.av = kap.clone();
                        } else {
                            x = fac_rs(&st, gg, 0, ceil_log2(d) as i32);
                        }
                        Ok(x)
                    };
                    claim(0, lm, &mut fac)?;
                }
            } else if p3 && (sn == "G" || sn == "U" || sn == "D") {
                for lm in 0..lam_m {
                    let lam = 2 * lm + 1;
                    let wk = ceil_log2(if sn == "D" { h.fe } else { d }) as i32;
                    let mut fac = |gg: &super::weights_layout::WsGrp| -> Result<WsFac> {
                        if gg.name == "kk" {
                            Ok(fac_rs(&st, gg, 0, wk))
                        } else if gg.name == "e" {
                            Ok(fac_rs(&st, gg, wk, le_))
                        } else {
                            fac_ew(gg, sn, if sn == "D" { 0 } else { h.fe })
                        }
                    };
                    let x_ = match sn {
                        "G" => 7,
                        "U" => 8,
                        _ => 10,
                    };
                    claim(x_, lam, &mut fac)?;
                }
            }
        }
    }
    if has_e {
        let ui = match ui_of.get(&(12u32, h.l as u32)) {
            Some(&u) => u,
            None => return Err(Refusal::internal(&format!("{}internal-claim-unit", f.g))),
        };
        let ke = cut_last(&ze, ze.len(), lt as usize)?;
        let mut pnt = tkh.clone();
        pnt.extend_from_slice(ke.hi);
        let et = eq_tab(ke.lo, lt as usize);
        let mut c = WsClaim { ui, f: Vec::new() };
        for gg in &inp.ws_lay.u[ui as usize].g {
            let mut x = WsFac::default();
            if gg.name == "v" {
                x.av = vec![E::zero(); h.v as usize];
                for tq in 0..t as usize {
                    x.av[inp.tokens[tq] as usize] = x.av[inp.tokens[tq] as usize] + et[tq];
                }
            } else {
                for i in 0..gg.z {
                    x.pt.push(pnt[(l_pd - gg.z + i) as usize]);
                }
                let e = eq_tab(&pnt, (l_pd - gg.z) as usize);
                for hi in 0..gg.o {
                    x.hv.push(e[hi as usize]);
                }
            }
            c.f.push(x);
        }
        claims.push(c);
    }
    if claims.len() as u64 != hp.n_cl as u64 {
        return Err(Refusal::internal(&format!("{}internal-claim-count", f.g)));
    }
    // The panels' values come from the batched sumcheck's end; v_E is sent separately.
    let mut s_va: Vec<u32> = (0..nclp).map(|a| s_v + a as u32).collect();
    let mut sve = 0u32;
    if has_e {
        sve = f.claims_in(tr, &mut slot, 1)?;
        s_va.push(sve);
    }
    let mut wo = ws_fork_end(f, tr, &mut slot, inp.ws_lay, &claims, &s_va, calls)?;
    // All points are known: the deferred tables get phi. Then the root of U3.
    for x in &later_phi {
        let want = (if x.lng { la } else { lt }) as usize;
        let pnt = match pt.get(&x.point) {
            Some(p) if p.len() == want => p,
            other => {
                let got = other.map(|p| p.len()).unwrap_or(usize::MAX);
                return Err(Refusal::internal(&format!(
                    "{}internal-g-table-point {} got={} want={}",
                    f.g, x.point, got, want
                )));
            }
        };
        let phi = if x.lng {
            long_phi(pnt, ls as usize, lt as usize)
        } else {
            eq_tab(pnt, lt as usize)
        };
        for q in 0..x.count {
            fun[x.first + q].phi = phi.clone();
        }
    }
    gate.root_in_h(f, tr, &[i_u3 as i32], calls)?;
    tl.close_funs(&fun)?;
    // The range check's messages.
    tl.transcript(f, tr, &mut slot, &t2, gate, calls)?;
    if slot != hp.used {
        return Err(Refusal::internal(&format!("{}internal-slot-count", f.g)));
    }
    f.plan_claims = hp.n_lin as u32;
    gate.batch(f, &mut t2, tr, slot, calls)?;
    // ---- The list of claims ----
    forest_objects(f, &fo)?;
    layer_object(f, &wpl)?;
    f.lin(&(Aff::slot(wpl.s_l) - Aff::slot(wpl.s_r)))?;
    {
        let txs = y.t_("xs")?;
        if txs.nl as u64 != y.xb.nl as u64
            || y.xb.nl as i32 != inp.limbs
            || nsl as u64 != 2 * y.xb.nl as u64 - 1
        {
            return Err(Refusal::named("plan-tensor-layout"));
        }
        let t_i = tab_at(&tab, "xbI@Z_V")?;
        let t_a = tab_at(&tab, "af@Z_V")?;
        let e = hi_tab(&wpl.r, la as usize, (l_ni as i32 + l_pd - ls as i32) as usize)?;
        let txsat = txs.at();
        let mut a = Aff::slot(wpl.s_l);
        for i in 0..ni {
            for kh in 0..ds2 {
                for l in 0..y.xb.nl as u64 {
                    let (tb, cell) = if i == 0 {
                        (t_i, ten_cell(&y.xb, l, 0, 0) / s2 + kh)
                    } else {
                        (t_a, ten_cell(&txsat, l, i - 1, 0) / s2 + kh)
                    };
                    a = a
                        + u3_at(f, i_u3, &tab_len, tb, cell)?
                            * (E::zero() - e[((i * y.pd) / s2 + kh) as usize] * gp[l as usize]);
                }
            }
        }
        f.lin(&a)?;
    }
    {
        {
            let mut a = Aff::slot(t_v.s_cl);
            for i in 0..(npl as u64 * ni) {
                a = a + Aff::slot(s_pv + i as u32) * (E::zero() - om_v[i as usize]);
            }
            f.lin(&a)?;
        }
        let mut s0 = E::zero();
        if inp.limbs == 5 {
            if no_l != 4 {
                return Err(Refusal::named("plan-tensor-layout"));
            }
            for i in 0..ni {
                s0 = s0
                    + led_products5(
                        &om_v[7 * i as usize..],
                        f.shown(t_v.s_end + (no_ol * i) as u32)?,
                        f.shown(t_v.s_end + (no_ol * i + 1) as u32)?,
                        f.shown(t_v.s_end + (no_ol * i + 2) as u32)?,
                        f.shown(t_v.s_end + (no_ol * i + 3) as u32)?,
                    );
            }
            let row_u = psc_row(f, &mut t_v.p, s0, &Aff::default())?;
            f.lin(&row_u)?;
            for i in 0..ni {
                let r = row5_at(f, i_u3, &tab, &tab_len, &trow, "r_tV", i)?;
                f.lin(&(Aff::slot(t_v.s_end + (no_ol * i) as u32) - r.a))?;
                f.lin(&(Aff::slot(t_v.s_end + (no_ol * i + 1) as u32) - r.b))?;
                f.lin(&(Aff::slot(t_v.s_end + (no_ol * i + 2) as u32) - r.rlo))?;
                f.lin(&(Aff::slot(t_v.s_end + (no_ol * i + 3) as u32) - r.rhi))?;
            }
            let mut rp: Vec<Row5<Aff>> = Vec::new();
            for i in 0..ni {
                rp.push(row5_at(f, i_u3, &tab, &tab_len, &trow, "P_V", i)?);
            }
            for i in 0..ni {
                for s in 0..9usize {
                    let ws = Aff::slot(s_w + (9 * i as u64 + s as u64) as u32);
                    f.lin(&led_carry5(&rp[i as usize], s, &ws))?;
                }
            }
            for i in 0..ni {
                let n = (i % 2) as usize;
                let mut pr = [Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default()];
                for j in 0..7u32 {
                    pr[j as usize] = Aff::slot(s_pv + (7 * i as u64 + j as u64) as u32);
                }
                let two = Aff::constant(ei(1i64 << (kl(inp.kl, g * lam + i / nn, if n != 0 { LM2 } else { LM1 }) + 1)));
                let mut out = [Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default(), Aff::default()];
                led_lines5(&rp[i as usize], &pr, ei(h.eps[n] as i64), &two, &mut out);
                for o in &out {
                    f.lin(o)?;
                }
            }
        } else {
            if no_l != 3 {
                return Err(Refusal::named("plan-tensor-layout"));
            }
            for i in 0..ni {
                s0 = s0
                    + om_v[3 * i as usize] * f.shown(t_v.s_end + (no_ol * i) as u32)? * f.shown(t_v.s_end + (no_ol * i) as u32)?
                    + om_v[3 * i as usize + 1] * f.shown(t_v.s_end + (no_ol * i + 1) as u32)? * f.shown(t_v.s_end + (no_ol * i) as u32)?
                    + om_v[3 * i as usize + 2] * f.shown(t_v.s_end + (no_ol * i + 2) as u32)? * f.shown(t_v.s_end + (no_ol * i) as u32)?;
            }
            let row_u = psc_row(f, &mut t_v.p, s0, &Aff::default())?;
            f.lin(&row_u)?;
            for i in 0..ni {
                let r = row_at(f, i_u3, &tab, &tab_len, &trow, "r_tV", i)?;
                f.lin(&(Aff::slot(t_v.s_end + (no_ol * i) as u32) - r.sig))?;
                f.lin(&(Aff::slot(t_v.s_end + (no_ol * i + 1) as u32) - r.rlo))?;
                f.lin(&(Aff::slot(t_v.s_end + (no_ol * i + 2) as u32) - r.rhi))?;
            }
            let mut rp: Vec<RowA> = Vec::new();
            for i in 0..ni {
                rp.push(row_at(f, i_u3, &tab, &tab_len, &trow, "P_V", i)?);
            }
            for i in 0..ni {
                for s in 0..7usize {
                    let r = &rp[i as usize];
                    f.lin(
                        &(Aff::slot(s_w + (7 * i as u64 + s as u64) as u32) + r.c[s].clone()
                            - r.dg[s].clone()
                            - r.c[s + 1].clone() * ei(256)),
                    )?;
                }
            }
            for i in 0..ni {
                let r = &rp[i as usize];
                let n = (i % 2) as usize;
                let mn = kl(inp.kl, g * lam + i / nn, if n != 0 { LM2 } else { LM1 });
                f.lin(&(r.v.clone() + Aff::constant(ei(h.eps[n] as i64))
                    - Aff::slot(s_pv + 3 * i as u32)
                    - r.l1.clone()))?;
                f.lin(&(r.l1.clone() + r.h1.clone() - r.sig.clone() * ei(2)))?;
                f.lin(&(Aff::slot(s_pv + (3 * i + 2) as u32) - r.p1.clone()))?;
                f.lin(
                    &(Aff::constant(ei(1i64 << (mn + 1))) + r.sig.clone()
                        - r.s0.clone()
                        - Aff::slot(s_pv + (3 * i + 1) as u32) * ei(2)
                        - r.p1.clone() * ei(1 << 25)
                        - r.rr.clone() * ei(2)),
                )?;
                f.lin(&(r.rr.clone() + r.rq.clone() - r.sig.clone() + Aff::constant(E::one())))?;
            }
        }
    }
    // What TSC(zt) has shown is a read at rt.
    if has_t {
        for i in 0..nn * lam {
            let form = row_r(f, i_u3, &tab, &tab_len, &trow, "rt", i, inp.limbs)?;
            f.lin(&(Aff::slot(t_t.as_ref().unwrap().s_end + i as u32) - form))?;
        }
        if p3 {
            for lm in 0..lam_m {
                f.lin(&(Aff::slot(s_sc + lm as u32) - ctx.sh(f, "sc", "rt", lm, 0)?))?;
            }
            for lm in 0..lam_m {
                for e in 0..ne {
                    f.lin(&(Aff::slot(s_sel + (lm * ne + e) as u32) - ctx.sh(f, "sel", "rt", lm, e)?))?;
                }
            }
        }
    }
    // The product layers for hh = s u. Their end values: -s, -u.
    layer_object(f, &hd)?;
    {
        let e = hi_tab(&hd.r, la as usize, (ll + l_pf as u32 - ls) as usize)?;
        let tab_a = tab_at(&tab, "af@Z_a")?;
        let ts = y.t_("s")?;
        let tu = y.t_("u")?;
        let mut a = Aff::slot(hd.s_l);
        let mut b = Aff::slot(hd.s_r);
        for lam in 0..lam {
            for kh in 0..h.f / s2 {
                let w = e[(lam * (y.pf / s2) + kh) as usize];
                a = a + long_a(f, i_u3, &tab_len, tab_a, ts, s2, lam, kh)? * w;
                b = b + long_a(f, i_u3, &tab_len, tab_a, tu, s2, lam, kh)? * w;
            }
        }
        f.lin(&a)?;
        f.lin(&b)?;
    }
    if p3 {
        let hd2 = hd2.as_ref().unwrap();
        layer_object(f, hd2)?;
        let e = hi_tab(&hd2.r, la as usize, (ll - 1 + lfe as u32 - ls) as usize)?;
        let tab_a = tab_at(&tab, "af@Z_b")?;
        let ts = y.t_("s")?;
        let tu = y.t_("u")?;
        let mut a = Aff::slot(hd2.s_l);
        let mut b = Aff::slot(hd2.s_r);
        for lm in 0..lam_m {
            for kh in 0..h.fe / s2 {
                let w = e[(lm * (h.fe / s2) + kh) as usize];
                a = a + long_a(f, i_u3, &tab_len, tab_a, ts, s2, 2 * lm + 1, h.fe / s2 + kh)? * w;
                b = b + long_a(f, i_u3, &tab_len, tab_a, tu, s2, 2 * lm + 1, h.fe / s2 + kh)? * w;
            }
        }
        f.lin(&a)?;
        f.lin(&b)?;
        // The selector's entries sum to 1.
        for lm in 0..lam_m {
            let mut a = Aff::constant(E::zero() - E::one());
            for e in 0..ne {
                a = a + ctx.sh(f, "sel", "zt", lm, e)? * E::one();
            }
            f.lin(&a)?;
        }
    }
    // The lookup's three claims on the multiplicity bits.
    {
        let t_b = [
            tab_at(&tab, "b-bits-0")?,
            tab_at(&tab, "b-bits-1")?,
        ];
        let t_p = tab_at(&tab, "b-pin")?;
        let w = (fo.k_t + 5 - h.lmb as i32) as u32;
        let cols = (fo.nc as u64) << w;
        let mut tb_vals: [Vec<Aff>; 2] = [Vec::new(), Vec::new()];
        for e in 0..2usize {
            for col in 0..cols {
                if col >= y.kbm {
                    return Err(Refusal::internal(&format!("{}internal-g-table-index", f.g)));
                }
                tb_vals[e].push(u3_at(f, i_u3, &tab_len, t_b[e], col)?);
            }
        }
        let mut tp_vals: Vec<Aff> = Vec::new();
        for col in 0..cols {
            if col >= y.kbm {
                return Err(Refusal::internal(&format!("{}internal-g-table-index", f.g)));
            }
            tp_vals.push(u3_at(f, i_u3, &tab_len, t_p, col)?);
        }
        forest_plane_lins(
            f,
            &mut fo,
            h.lmb as i32,
            |e, x| tb_vals[e as usize][x as usize].clone(),
            |x| tp_vals[x as usize].clone(),
        )?;
    }
    // The embedding's value is a read of the first stream (G_0 only).
    if has_e {
        let e = eq_tab(&tkh, (l_pd - ls as i32) as usize);
        let t = tab_at(&tab, "xbI@Z_E")?;
        let mut a = Aff::slot(sve) * (E::zero() - E::one());
        for kh in 0..ds2 {
            a = a + xb_a(f, i_u3, &tab_len, t, y.xb.nl as u64, &y.xb, s2, kh)? * e[kh as usize];
        }
        f.lin(&a)?;
    }
    if tl.fold_drawn != 1 {
        return Err(Refusal::internal(&format!("{}internal-g-rows-booked", f.g)));
    }
    if 1 + tl.groups_run() != 2 {
        return Err(Refusal::internal(&format!("{}internal-g-calls-booked", f.g)));
    }
    tl.objects(f, &fun)?;
    f.lin(&row_s)?;
    forest_join_added(&fo)?;
    f.lin(&(Aff::slot(s_a0) - a_lin))?;
    f.lin(&(Aff::slot(s_b0) - b_lin))?;
    ws_fork_lin(f, &mut wo.merged)?;
    for j in 0..hp.used {
        if (f.ls[j as usize] == E::zero()) != (j == wo.merged.s_fv) {
            return Err(Refusal::internal(&format!("{}internal-g-free-slot", f.g)));
        }
    }
    if f.n_claim as usize != hp.n_lin {
        return Err(Refusal::internal(&format!("{}internal-g-claim-count", f.g)));
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
    Ok(LayerRunOut {
        wo,
        nc,
        nm: tl.nm,
        n_claim: f.n_claim,
        n_slots: f.ns,
    })
}

/// One digit row with four limbs (`rowAt`).
fn row_at(
    f: &HFork,
    i_u3: u32,
    tab: &BTreeMap<String, u64>,
    tab_len: &BTreeMap<u64, u64>,
    trow: &super::stage_layout::Ten,
    p: &str,
    i: u64,
) -> Result<RowA> {
    let t = tab_at(tab, &format!("ar@{}", p))?;
    let mut r = RowA::default();
    for j in 0..74u64 {
        r.dg[j as usize] = u3_at(f, i_u3, tab_len, t, trow.off + i * 74 + j)? + Aff::constant(ei(128));
    }
    let dig = |r: &RowA, a: usize, n: usize| -> Aff {
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

/// One digit row with five limbs (`row5At`).
fn row5_at(
    f: &HFork,
    i_u3: u32,
    tab: &BTreeMap<String, u64>,
    tab_len: &BTreeMap<u64, u64>,
    trow: &super::stage_layout::Ten,
    p: &str,
    i: u64,
) -> Result<Row5<Aff>> {
    let t = tab_at(tab, &format!("ar@{}", p))?;
    let mut cells: Vec<Aff> = Vec::with_capacity(99);
    for j in 0..99u64 {
        cells.push(u3_at(f, i_u3, tab_len, t, trow.off + i * 99 + j)?);
    }
    Ok(row5(|j| cells[j].clone()))
}

/// `rowR(P, i)`: the reciprocal of digit row i.
fn row_r(
    f: &HFork,
    i_u3: u32,
    tab: &BTreeMap<String, u64>,
    tab_len: &BTreeMap<u64, u64>,
    trow: &super::stage_layout::Ten,
    p: &str,
    i: u64,
    limbs: i32,
) -> Result<Aff> {
    if limbs == 5 {
        Ok(row5_at(f, i_u3, tab, tab_len, trow, p, i)?.r)
    } else {
        Ok(row_at(f, i_u3, tab, tab_len, trow, p, i)?.r)
    }
}

fn is_acc(s: &str) -> bool {
    matches!(s, "G" | "U" | "V" | "O" | "D" | "LR")
}

/// One panel of the batched sumcheck (`SBlk`, vf_layers_check.inc:572-586). `a`/`b` are
/// `ni * ny` forms, row-major; a `tri` panel has `sl`/`xx` instead.
#[derive(Clone, Default)]
struct Panel {
    tri: bool,
    v0: i64,
    claim: usize,
    ec: E,
    ni: u64,
    ny: u64,
    wy: u32,
    w: u32,
    off: u64,
    a: Vec<Aff>,
    b: Vec<Aff>,
    wt: Vec<E>,
    sl: Vec<E>,
    xx: Vec<Aff>,
    virt: i64,
}

#[allow(clippy::too_many_arguments)]
fn push_panel(
    bl: &mut Vec<Panel>,
    claim: usize,
    ec: E,
    ni: u64,
    ny: u64,
    a: Vec<Aff>,
    b: Option<Vec<Aff>>,
    wt: Vec<E>,
    next_v: &mut i64,
) {
    let wy = ceil_log2(ny) as u32;
    let w = ceil_log2(ni) as u32 + wy;
    let (v0, bb) = match b {
        Some(x) => (-1, x),
        None => {
            let v = *next_v;
            *next_v += ni as i64;
            (v, Vec::new())
        }
    };
    bl.push(Panel {
        tri: false,
        v0,
        claim,
        ec,
        ni,
        ny,
        wy,
        w,
        off: 0,
        a,
        b: bb,
        wt,
        sl: Vec::new(),
        xx: Vec::new(),
        virt: -1,
    });
}

#[allow(clippy::too_many_arguments)]
fn push_tri(
    bl: &mut Vec<Panel>,
    claim: usize,
    ec: E,
    ne: u64,
    nk: u64,
    sl: Vec<E>,
    xx: Vec<Aff>,
    virt: i64,
    wt: E,
    le: u32,
    next_v: &mut i64,
) {
    let wy = ceil_log2(nk) as u32;
    let v0 = *next_v;
    *next_v += 1;
    bl.push(Panel {
        tri: true,
        v0,
        claim,
        ec,
        ni: ne,
        ny: nk,
        wy,
        w: le + wy,
        off: 0,
        a: Vec::new(),
        b: Vec::new(),
        wt: vec![wt],
        sl,
        xx,
        virt,
    });
}

/// `joinPart(c, q)` (vf_layers_check.inc:547-566).
fn join_part(
    ctx: &Ctx<'_>,
    f: &HFork,
    yy: &Lay,
    q: usize,
    laid: &mut [u64],
    has_t: bool,
) -> Result<Aff> {
    let c = &yy.calls[q];
    let el = eq_tab(zl(c), ctx.ll as usize);
    let e = eq_tab(zj(c, ctx.ll), c.l_j as usize);
    let mut weighed = vec![false; (ctx.lam * c.j) as usize];
    let mut lines = Aff::default();
    for lam in 0..ctx.lam {
        for s in &c.segs {
            if s.moe && !(ctx.p3 && lam % 2 == 1) {
                continue;
            }
            lines = lines + ctx.line(f, &s.name, lam)? * (E::zero() - el[lam as usize]);
            for x in 0..s.n {
                let at = (lam * c.j + s.pos[x as usize]) as usize;
                if weighed[at] {
                    return Err(Refusal::named("internal-g-join-place"));
                }
                weighed[at] = true;
            }
        }
    }
    let mut pad_w = E::zero();
    let shift = (ctx.fo.d_t - ctx.lt as i32) as u32;
    for lam in 0..ctx.lam {
        let mut sum = E::zero();
        for j in 0..c.j {
            if !weighed[(lam * c.j + j) as usize] {
                sum = sum + e[j as usize];
                laid[ctx.fo.first[q] as usize + ((lam * c.j + j) >> shift) as usize] += ctx.t;
            }
        }
        pad_w = pad_w + el[lam as usize] * sum;
    }
    Ok(Aff::constant(
        ctx.fo.alpha - e_scale(ctx.fo.theta, q as u64) - e_scale(pad_w, c.c.tau_at(c.c.t0)),
    ) + lines)
}

fn l_ni_usize(n: u64) -> usize {
    let mut b = 0usize;
    while (1u64 << b) < n {
        b += 1;
    }
    b
}

fn mu_v_usize(inp: &LayerCheckInputs<'_>) -> usize {
    let l_ni = l_ni_usize(inp.y.ni) as i32;
    (l_ni + inp.y.l_pd + inp.h.lt as i32) as usize
}
