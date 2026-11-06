//! The shape of one layer group's attention sub-proof, ported from
//! `verifier/src/vf_attention_shape.h` (and `aforkShapeHid` from `vf_attention_check.h`).
//!
//! From the public parameters (`ACfg`), [`AFork::shape`] derives sizes, lookup tables and calls,
//! and tests the no-overflow conditions against wrap-around in the field. [`ten_cell`] to
//! [`head_feat`] serve all sub-proofs. The C++ module-level `refuse()` becomes a [`Refusal`].
//!
//! The lookup forest ([`super::lookup::HForest`]) is built by [`afork_shape_hid`]; it needs `LIDB`
//! from the stage state, passed as `lid`.

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::numbers::codes::ceil_log2;
use crate::refusal::{Refusal, Result};

use super::common::{eq_tab, Call, WPE};
use super::lookup::{
    forest_plane_cols, forest_pub_ask, forest_shape, HForest,
};

/// `CLAMP`: lookup table FC clamps queries, keys and values to `-CLAMP .. CLAMP`.
pub const CLAMP: i32 = 2047;

/// `CLAMPED_CELL_BOUND`: the bound on a clamped cell in the layer and output-head conditions.
pub const CLAMPED_CELL_BOUND: u32 = CLAMP as u32 + 1;

/// A tensor's features in a committed matrix (`struct TenAt`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TenAt {
    pub off: u64,
    pub nl: u64,
    pub cnt: u64,
    pub j: u64,
}

/// `tenCell(X, l, i, j)`: the matrix's feature that stores limb `l` of feature `j` at layer `i`.
pub fn ten_cell(x: &TenAt, l: u64, i: u64, j: u64) -> u64 {
    x.off + (l * x.cnt + i) * x.j + j
}

/// `blockRow(c2, t, T)`.
pub fn block_row(c2: usize, t: usize, t_count: usize) -> usize {
    c2 * t_count + t
}

/// `blockRows(low, tok)`.
pub fn block_rows(low: &[E], tok: &[E]) -> Vec<E> {
    let mut v = vec![E::zero(); low.len() * tok.len()];
    for c2 in 0..low.len() {
        for t in 0..tok.len() {
            v[block_row(c2, t, tok.len())] = low[c2] * tok[t];
        }
    }
    v
}

/// `longPoint(low, ls, tok)`.
pub fn long_point(low: &[E], ls: usize, tok: &[E]) -> Vec<E> {
    let mut p = low[..ls].to_vec();
    p.extend_from_slice(tok);
    p
}

/// `longPhi(p, ls, lt)`.
pub fn long_phi(p: &[E], ls: usize, lt: usize) -> Vec<E> {
    block_rows(&eq_tab(p, ls), &eq_tab(&p[ls..], lt))
}

/// A point split in two (`struct PointHighLow`).
#[derive(Clone, Copy, Debug)]
pub struct PointHighLow<'a> {
    pub hi: &'a [E],
    pub lo: &'a [E],
    pub nhi: usize,
}

/// `cutLast(z, n, k)`.
pub fn cut_last(z: &[E], n: usize, k: usize) -> Result<PointHighLow<'_>> {
    if k > n {
        return Err(Refusal::named("plan-tensor-layout"));
    }
    Ok(PointHighLow { hi: &z[..n - k], lo: &z[n - k..], nhi: n - k })
}

/// `lastOf(z, k)`.
pub fn last_of(z: &[E], k: usize) -> Result<Vec<E>> {
    Ok(cut_last(z, z.len(), k)?.lo.to_vec())
}

/// `hiTab(z, la, want)`.
pub fn hi_tab(z: &[E], la: usize, want: usize) -> Result<Vec<E>> {
    let c = cut_last(z, z.len(), la)?;
    if c.nhi != want {
        return Err(Refusal::named("plan-tensor-layout"));
    }
    Ok(eq_tab(c.hi, c.nhi))
}

/// `headFeat(X, hd, dh)`.
pub fn head_feat(x: &TenAt, hd: u64, dh: u64) -> Result<u64> {
    if dh == 0 || x.j % dh != 0 || hd >= x.j / dh {
        return Err(Refusal::named("plan-tensor-layout"));
    }
    Ok(hd * dh)
}

/// The lookup segments' enum (`ASeg`): RM, RD, FM, FD, WL, WH, IX.
pub const S_RM: i32 = 0;
pub const S_RD: i32 = 1;
pub const S_FM: i32 = 2;
pub const S_FD: i32 = 3;
pub const S_WL: i32 = 4;
pub const S_WH: i32 = 5;
pub const S_IX: i32 = 6;

/// The public parameters of one attention sub-proof (`struct ACfg`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ACfg {
    pub lt: i32,
    pub l_b: i32,
    pub lgk: i32,
    pub ldh: i32,
    pub ll: i32,
    pub s: i32,
    pub rx: i32,
    pub k_fd: i32,
    pub lm_s: i32,
    pub la: i32,
    pub lmb: i32,
    pub nmin: i32,
    pub h: u64,
    /// One shift per layer.
    pub sh: Vec<u32>,
    pub wc_h: u64,
    pub wc_o: u64,
    pub wc_q: u64,
    pub n_as: u64,
    pub ty: u128,
    pub o_in_qa: bool,
    pub lines: Vec<Line>,
}

/// One line of the call list (`ACfg::Line`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Line {
    pub name: String,
    pub kind: String,
    pub segs: Vec<i32>,
}

/// One piece of a lookup call (`struct APiece`): `2^b` keys of one segment.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct APiece {
    pub seg: i32,
    pub lam: u64,
    pub a: u64,
    pub b: i32,
    pub off: u64,
}

/// One expanded call (`struct ACall`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ACall {
    pub c: Call,
    pub kind: String,
    pub sh: u32,
    pub segs: Vec<i32>,
    pub pcs: Vec<APiece>,
    /// The sum of the pieces' sizes: the keys from `tot` on are padding keys.
    pub tot: u64,
    pub tau: Vec<u64>,
}

/// `eqAt(z, n, idx)`: coordinate 0 is the top bit.
pub fn eq_at(z: &[E], n: usize, idx: u64) -> E {
    let mut p = E::one();
    for v in 0..n {
        p = p * if (idx >> (n - 1 - v)) & 1 != 0 { z[v] } else { E::one() - z[v] };
    }
    p
}

/// `eqPts(x, y, n)`.
pub fn eq_pts(x: &[E], y: &[E], n: usize) -> E {
    let mut p = E::one();
    for v in 0..n {
        p = p * (x[v] * y[v] + (E::one() - x[v]) * (E::one() - y[v]));
    }
    p
}

/// `onesOf(z, n)`.
pub fn ones_of(z: &[E], n: usize) -> E {
    let mut p = E::one();
    for v in 0..n {
        p = p * z[v];
    }
    p
}

/// `idOf(z, n)`.
pub fn id_of(z: &[E], n: usize) -> E {
    let mut s = E::zero();
    for v in 0..n {
        s = s + E::from_base(crate::field::ext::F::from_u64(1u64 << (n - 1 - v))) * z[v];
    }
    s
}

/// `LEof(x, y, n)`: the multilinear extension of the non-strict comparison, by a recurrence from
/// the lowest bit.
pub fn le_of(x: &[E], y: &[E], n: usize) -> E {
    let mut le = E::one();
    for v in (0..n).rev() {
        le = (E::one() - x[v]) * y[v]
            + (x[v] * y[v] + (E::one() - x[v]) * (E::one() - y[v])) * le;
    }
    le
}

/// What `shape()` derives from the configuration (`struct AFork`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AFork {
    pub cf: ACfg,
    pub t: u64,
    pub b: u64,
    pub n_t: u64,
    pub h_p: u64,
    pub g: u64,
    pub ha: u64,
    pub dh: u64,
    pub dq: u64,
    pub dkv: u64,
    pub lam: u64,
    pub u0: u64,
    pub ln_t: i32,
    pub n_m: i32,
    pub n_d: i32,
    pub ls: i32,
    pub tt: Vec<u64>,
    pub calls: Vec<ACall>,
    pub k_as: u64,
    pub kb_a: u64,
    pub feat_h: u64,
    pub feat_o: u64,
    pub feat_q: u64,
    pub fill_h: u64,
    pub fill_o: u64,
    pub fill_q: u64,
    pub o_mr: u64,
    pub o_zr: u64,
    pub o_ib: u64,
    pub o_rh: u64,
    pub o_rhp: u64,
    pub o_q: u64,
    pub o_k: u64,
    pub o_v: u64,
    pub o_o: u64,
    pub at_q: TenAt,
    pub at_k: TenAt,
    pub at_v: TenAt,
    pub at_o: TenAt,
    pub smax: u64,
}

/// The softmax shift's derived numbers (`AFork::ShD`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ShD {
    pub c: u64,
    pub rho: u64,
    pub n_hd: u64,
    pub om: u64,
}

impl AFork {
    /// `AFork::shd(sh)`.
    pub fn shd(&self, sh: u32) -> ShD {
        let c = self.u0 << sh;
        let rho = 65536 - (1u64 << sh);
        let n_hd = (4 * self.smax + 1 + rho - 1) / rho;
        ShD { c, rho, n_hd, om: 2 * self.smax + c }
    }

    /// `AFork::segB(s)`.
    pub fn seg_b(&self, s: i32) -> u64 {
        match s {
            S_RM | S_FM => self.n_m as u64,
            S_RD | S_FD => self.n_d as u64,
            S_WL => 1 + self.cf.lgk as u64 + self.cf.lt as u64 + self.cf.ldh as u64,
            S_WH => self.cf.lgk as u64 + self.cf.lt as u64 + self.cf.ldh as u64,
            _ => self.cf.lgk as u64 + self.cf.lt as u64,
        }
    }

    /// `AFork::shape()`: reads no proof.
    pub fn shape(&mut self) -> Result<()> {
        let lt = self.cf.lt;
        if lt < 2 || lt > 16 || self.cf.l_b < 0 || self.cf.l_b > lt - 2 {
            return Err(Refusal::named("af-shape-tiles"));
        }
        self.t = 1u64 << lt;
        self.b = 1u64 << self.cf.l_b;
        self.ln_t = lt - self.cf.l_b;
        self.n_t = 1u64 << self.ln_t;
        self.h_p = self.n_t / 2;
        self.g = 1u64 << self.cf.lgk;
        if self.cf.h == 0 || self.cf.h % self.g != 0 {
            return Err(Refusal::named("af-shape-heads"));
        }
        self.ha = self.cf.h / self.g;
        self.dh = 1u64 << self.cf.ldh;
        self.dq = self.cf.h * self.dh;
        self.dkv = self.g * self.dh;
        self.lam = 1u64 << self.cf.ll;
        if self.cf.sh.len() != self.lam as usize {
            return Err(Refusal::named("af-shape-sh"));
        }
        self.ls = self.cf.la - lt;
        if self.ls < 0 || self.ls > self.cf.ldh || self.cf.la > 16 {
            return Err(Refusal::named("af-shape-la"));
        }
        if self.cf.s < 1
            || self.cf.s > 14
            || self.cf.rx < 1
            || self.cf.rx > 12
            || lt + self.cf.s + 1 > 24
        {
            return Err(Refusal::named("af-policy-softmax"));
        }
        self.tt.clear();
        // Rounding is to nearest, ties to even: nearbyint under the default rounding mode.
        let mut u = 0u64;
        loop {
            let v = libm::rint(
                libm::ldexp(1.0, self.cf.s as i32)
                    * libm::exp(-(u as f64) / libm::ldexp(1.0, self.cf.rx as i32)),
            );
            if v == 0.0 {
                self.u0 = u;
                break;
            }
            self.tt.push(v as u64);
            if u > (1u64 << 20) {
                return Err(Refusal::named("af-policy-softmax"));
            }
            u += 1;
        }
        self.smax = self.dh * CLAMP as u64 * CLAMP as u64;
        self.n_m = self.cf.lgk + 2 * lt - 1;
        self.n_d = self.cf.lgk + lt + self.cf.l_b;
        if self.cf.lm_s > self.n_d || self.cf.lm_s < 1 {
            return Err(Refusal::named("af-shape-lmS"));
        }
        let p2: u128 = 1u128 << 60;
        let p: u128 = (1u128 << 61) - 1;
        let ty = self.cf.ty;
        let ty2 = ty * 257;
        let ty4 = ty * 16843009u128;
        let mut shs = self.cf.sh.clone();
        shs.sort_unstable();
        shs.dedup();
        if self.cf.k_fd < 8 || self.cf.k_fd > 16 {
            return Err(Refusal::named("af-policy-kF"));
        }
        for &sh in &shs {
            if !(4..=12).contains(&sh) {
                return Err(Refusal::named("af-policy-sh"));
            }
            let d = self.shd(sh);
            let rows = 1u64 << self.cf.k_fd;
            if rows < self.u0 + d.n_hd || rows - self.u0 - d.n_hd > d.n_hd {
                return Err(Refusal::named("af-policy-kF"));
            }
            if d.c + 65536 > (1u64 << 24) {
                return Err(Refusal::named("af-policy-C"));
            }
            if !(6 * self.smax as u128
                + 2 * d.c as u128
                + 3 * 65536
                + (1u128 << 32)
                + (1u128 << 33) * (ty2 + 128 + (1u128 << self.cf.s))
                < p)
            {
                return Err(Refusal::named("af-no-wrap-N3"));
            }
            if !(6 * self.smax as u128 + 2 * d.c as u128 + 3 * 65536 < (1u128 << 32)) {
                return Err(Refusal::named("af-no-wrap-N4"));
            }
        }
        if !((ty4 + self.smax as u128) < p2) {
            return Err(Refusal::named("af-no-wrap-N1"));
        }
        if !((1u128 << 40) * ty
            + (1u128 << 20) * (ty + 128)
            + ty
            + 128
            + (1u128 << 41)
            < p
            && ty + 128 + 256 < (1u128 << 20))
        {
            return Err(Refusal::named("af-no-wrap-N2"));
        }
        let ts: u128 = (self.t as u128) << self.cf.s;
        if !(ts + ty4 < p2) {
            return Err(Refusal::named("af-no-wrap-N5"));
        }
        if !(2 * ts * CLAMP as u128
            + ts
            + 2 * ts * ty2
            + 2 * ts
            + 1
            + 65536 * (ty + 128)
            + 65536
            < p2)
        {
            return Err(Refusal::named("af-no-wrap-N6"));
        }
        if !(((1u128 << (16 - lt)) * 2 * self.t as u128) < p2) {
            return Err(Refusal::named("af-no-wrap-N9"));
        }
        // The expanded list. If sh has several values, a KR or KFD call's name ends in its sh.
        self.calls.clear();
        let one = shs.len() == 1;
        let sfx = |sh: u32| if one { String::new() } else { format!("{}", sh) };
        for l in &self.cf.lines {
            if l.segs.is_empty() {
                return Err(Refusal::named("af-policy-call-list"));
            }
        }
        {
            let mut seen = [0i32; 7];
            for l in &self.cf.lines {
                for &s in &l.segs {
                    if !(0..=6).contains(&s) {
                        return Err(Refusal::named("af-policy-call-list"));
                    }
                    let ok = (l.kind == "KR" && (s == S_RM || s == S_RD))
                        || (l.kind == "KFD" && (s == S_FM || s == S_FD))
                        || (l.kind == "R16" && (s == S_WL || s == S_IX))
                        || (l.kind == "WH" && s == S_WH);
                    if !ok || seen[s as usize] != 0 {
                        return Err(Refusal::named("af-policy-call-list"));
                    }
                    seen[s as usize] += 1;
                }
            }
            if seen.iter().any(|&x| x == 0) {
                return Err(Refusal::named("af-policy-call-list"));
            }
        }
        for l in &self.cf.lines {
            if l.kind.starts_with('K') {
                for &sh in &shs {
                    let mut c = ACall::default();
                    c.c.name = format!("{}{}", l.name, sfx(sh));
                    c.kind = l.kind.clone();
                    c.sh = sh;
                    c.segs = l.segs.clone();
                    self.calls.push(c);
                }
            } else {
                let mut c = ACall::default();
                c.c.name = l.name.clone();
                c.kind = l.kind.clone();
                c.sh = 0;
                c.segs = l.segs.clone();
                self.calls.push(c);
            }
        }
        if self.cf.nmin < 10 {
            return Err(Refusal::named("af-policy-nmin"));
        }
        if (1u64 << self.cf.la) > self.cf.wc_o * self.t
            || (1u64 << self.cf.la) > self.cf.wc_q * self.t
            || self.cf.wc_o % (1u64 << self.ls) != 0
            || self.cf.wc_q % (1u64 << self.ls) != 0
        {
            return Err(Refusal::named("af-shape-la"));
        }
        if self.calls.len() > 12 {
            return Err(Refusal::named("af-policy-call-list"));
        }
        for q in 0..self.calls.len() {
            let by_sh = self.calls[q].kind.starts_with('K');
            let mut pcs = Vec::new();
            let segs = self.calls[q].segs.clone();
            let sh = self.calls[q].sh;
            for s in segs {
                for lam in 0..self.lam {
                    if by_sh && self.cf.sh[lam as usize] != sh {
                        continue;
                    }
                    for a in 0..self.ha {
                        pcs.push(APiece { seg: s, lam, a, b: self.seg_b(s) as i32, off: 0 });
                    }
                }
            }
            pcs.sort_by(|x, y| y.b.cmp(&x.b));
            let mut off = 0u64;
            for pc in &mut pcs {
                pc.off = off;
                off += 1u64 << pc.b;
            }
            self.calls[q].pcs = pcs;
            self.calls[q].tot = off;
            let mut n = ceil_log2(off) as i32;
            if n < self.cf.nmin {
                n = self.cf.nmin;
            }
            self.calls[q].c.n = n;
            self.calls[q].c.kappa = 5;
            if n < 10 || n > 44 {
                let name = self.calls[q].c.name.clone();
                return Err(Refusal::named(&format!("af-shape-call-{}", name)));
            }
            match self.calls[q].kind.as_str() {
                "KR" => {
                    self.calls[q].c.k = 16;
                    self.calls[q].c.func = 2;
                    let sh = self.calls[q].sh;
                    self.calls[q].tau = (0..65536u64)
                        .map(|t| (t & 255) + ((t >> 8) << 20) + (((t >= (1u64 << sh)) as u64) << 40))
                        .collect();
                }
                "WH" => {
                    self.calls[q].c.k = 16;
                    self.calls[q].c.func = 2;
                    self.calls[q].tau =
                        (0..65536u64).map(|t| (t & 255) + ((t >> 8) << 20)).collect();
                }
                "R16" => {
                    self.calls[q].c.k = 16;
                    self.calls[q].c.func = 0;
                }
                _ => {
                    let d = self.shd(self.calls[q].sh);
                    let n_h = d.n_hd;
                    let sh = self.calls[q].sh;
                    self.calls[q].c.k = self.cf.k_fd;
                    self.calls[q].c.func = 1;
                    self.calls[q].c.t0 = self.u0;
                    let size = 1usize << self.cf.k_fd;
                    self.calls[q].tau = (0..size as u64)
                        .map(|t| {
                            if t < self.u0 {
                                (t << sh) + (self.tt[t as usize] << 33)
                            } else if t < self.u0 + n_h {
                                d.c - (1u64 << sh) + d.rho * (t - self.u0) + (1u64 << 32)
                            } else {
                                d.c - (1u64 << sh)
                                    + d.rho * (t - self.u0 - n_h)
                                    + d.rho / 2
                                    + (1u64 << 32)
                            }
                        })
                        .collect();
                }
            }
        }
        {
            let cells = 5 * self.lam * self.ha * ((1u64 << self.n_m) + (1u64 << self.n_d));
            let unit = self.cf.n_as << self.cf.lm_s;
            self.k_as = (cells + unit - 1) / unit * self.cf.n_as;
        }
        self.o_mr = 0;
        self.o_zr = 4 * self.lam * self.cf.h;
        self.o_ib = 8 * self.lam * self.cf.h;
        self.feat_h = self.o_ib + self.lam * lt as u64 * self.cf.h;
        self.o_rh = 0;
        self.o_rhp = self.lam * self.dq;
        self.feat_o = 2 * self.lam * self.dq;
        self.o_q = 0;
        self.o_k = 2 * self.lam * self.dq;
        self.o_v = self.o_k + 2 * self.lam * self.dkv;
        self.o_o = self.o_v + 2 * self.lam * self.dkv;
        self.feat_q = self.o_o + if self.cf.o_in_qa { 2 * self.lam * self.dq } else { 0 };
        self.at_q = TenAt { off: self.o_q, nl: 2, cnt: self.lam, j: self.dq };
        self.at_k = TenAt { off: self.o_k, nl: 2, cnt: self.lam, j: self.dkv };
        self.at_v = TenAt { off: self.o_v, nl: 2, cnt: self.lam, j: self.dkv };
        self.at_o = TenAt { off: self.o_o, nl: 2, cnt: self.lam, j: self.dq };
        self.fill_h = (self.feat_h + self.cf.wc_h - 1) / self.cf.wc_h * self.cf.wc_h;
        self.fill_o = (self.feat_o + self.cf.wc_o - 1) / self.cf.wc_o * self.cf.wc_o;
        self.fill_q = (self.feat_q + self.cf.wc_q - 1) / self.cf.wc_q * self.cf.wc_q;
        Ok(())
    }

    /// `AFork::bindTau()`: points each call at its own `tau` vector.
    pub fn bind_tau(&mut self) {
        for c in &mut self.calls {
            c.c.tau = if c.tau.is_empty() { None } else { Some(c.tau.clone()) };
        }
    }

    /// `AFork::tableWords()`.
    pub fn table_words(&self) -> usize {
        let mut n_kf = 0usize;
        for c in &self.calls {
            if c.kind == "KFD" {
                n_kf += c.segs.len();
            }
        }
        WPE * (3 * self.k_as as usize
            + (n_kf + 6) * self.fill_h as usize
            + ((self.fill_o * self.t) >> self.cf.la) as usize
            + (2 * n_kf + 5) * ((self.fill_q * self.t) >> self.cf.la) as usize
            + 3 * self.kb_a as usize)
    }

    /// `AFork::cover(P, sg, I, J)`: the score tile `(I, J)`, `J < I`, in slot `sg` of slot row `P`.
    pub fn cover(&self, p: u64, sg: u64) -> (u64, u64) {
        if sg < p {
            (p, sg)
        } else {
            (self.n_t - 1 - p, sg - p)
        }
    }
}

/// `aforkShapeHid`: the shape of A_g's one lookup group, all of `A.calls`. It runs `A.shape()`,
/// so only `A.cf` must be filled, and reads no proof. Rejects a call that is all padding, and sets
/// `pub`, each call's `iota` and `A.kbA`, the columns of `bA_g`.
pub fn afork_shape_hid(a: &mut AFork, lid: i32) -> Result<HForest> {
    a.shape()?;
    let calls: Vec<Call> = a.calls.iter().map(|c| c.c.clone()).collect();
    let mut h = forest_shape(&calls, lid)?;
    // run() builds one table TA (TO) from the last lmS (lt + ldh) coordinates of several calls'
    // key points (zk). Only the last dT coordinates, zx, are the same in all calls.
    if h.d_t < a.cf.lm_s.max(a.cf.lt + a.cf.ldh) {
        return Err(Refusal::named("forest-depth-A"));
    }
    a.kb_a = forest_plane_cols(&h, a.cf.lmb)?;
    for q in 0..a.calls.len() {
        a.calls[q].c.iota = h.iota[q];
    }
    h.pub_ = vec![0; h.nt as usize];
    for q in 0..a.calls.len() {
        let n = a.calls[q].c.n;
        let tot = a.calls[q].tot;
        h.pub_run(q as i32, tot, (1u64 << n) - tot)?;
    }
    let names = h.names.clone();
    let pub_ = h.pub_.clone();
    forest_pub_ask(&h, &names, &pub_, "")?;
    Ok(h)
}
