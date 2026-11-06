//! The layout of the committed weight matrix W and a sub-proof's claims about W, ported from
//! `verifier/src/vf_weights_layout.h`.
//!
//! A layer or output-head sub-proof has claims about the weights, each about one unit: the rows of
//! W that store one layer's weights of one kind, the embedding, or the output head.
//! [`ws_fork_end`] runs the merge and reduces the claims to row weights; the pending claim on W is
//! built by [`super::weights_pending::ws_pending`].

use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::codes::ceil_log2;
use crate::refusal::{Refusal, Result};

use super::common::eq_tab;
use super::engine::HFork;
use super::packing::e_scale;
use super::transcript::Tr;
use super::weights_merge::{ws_fork_merge, WsMerged};

/// W has at most `2^WS_ROWS_MOST_LOG2` rows.
pub const WS_ROWS_MOST_LOG2: u32 = 22;
/// A weight is the sum over `j` of `WS_SECOND_DIGIT^j` times its digit `j`.
pub const WS_SECOND_DIGIT: u32 = 256;

/// `WsShape`: the public sizes of W.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WsShape {
    pub d: u64,
    pub l: u64,
    pub dd: u64,
    pub dh: u64,
    pub dkv: u64,
    pub dq: u64,
    pub f: u64,
    pub fe: u64,
    pub ne: u64,
    pub v: u64,
    pub eh: u32,
    pub moe_flag: u32,
    pub moe: Vec<u8>,
}

/// `wsSetMoe`.
pub fn ws_set_moe(s: &mut WsShape, moe: bool) {
    s.moe_flag = if moe { 1 } else { 0 };
    s.moe = vec![0; if s.l <= 4096 { s.l as usize } else { 0 }];
    for l in 0..s.moe.len() {
        s.moe[l] = (moe && (l & 1) != 0) as u8;
    }
}

/// An index group (`struct WsGrp`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WsGrp {
    pub name: &'static str,
    pub r: u64,
    pub o: u64,
    pub left: u64,
    pub cls: u8, // b'E' or b'A'
    pub high: bool,
    pub z: i32,
    pub t: i32,
    pub cb0: i32,
}

impl WsGrp {
    /// `takenBit(b)`.
    pub fn taken_bit(&self, b: i32) -> bool {
        if self.high {
            b >= self.z - self.t
        } else {
            b < self.t
        }
    }

    /// `takenAt(i)`: the `i`-th taken bit, lowest first.
    pub fn taken_at(&self, i: i32) -> i32 {
        if self.high {
            self.z - self.t + i
        } else {
            i
        }
    }

    /// `aTaken()`: a class A group with `R = 1` counts as not taken.
    pub fn a_taken(&self) -> bool {
        self.cls == b'A' && self.t > 0
    }
}

/// One unit's rows in W (`struct WsUnit`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WsUnit {
    pub x: u32,
    pub l: u32,
    pub nlw: i32,
    pub ncb: i32,
    pub g: Vec<WsGrp>,
    pub rows: u64,
    pub off: u64,
}

/// W's layout (`struct WsLay`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WsLay {
    pub lk: i32,
    pub m0: u64,
    pub u: Vec<WsUnit>,
}

impl WsLay {
    /// `WsLay::E_`.
    pub fn e_(n: &'static str, r: u64, high: bool) -> WsGrp {
        let mut g = WsGrp {
            name: n,
            r,
            o: r,
            left: 0,
            cls: b'E',
            high,
            z: 0,
            t: 0,
            cb0: 0,
        };
        while g.o & 1 == 0 {
            g.o >>= 1;
            g.z += 1;
        }
        g
    }

    /// `WsLay::A_`.
    pub fn a_(n: &'static str, r: u64) -> WsGrp {
        WsGrp { name: n, r, o: 0, left: 0, cls: b'A', high: false, z: 0, t: 0, cb0: 0 }
    }

    /// `WsLay::add`: appends a unit from row `m0` on.
    pub fn add(&mut self, x: u32, l: u32, nlw: i32, mut g: Vec<WsGrp>) -> Result<()> {
        let mut left = self.lk;
        let mut cb = 0i32;
        let mut rows: u128 = nlw as u128;
        for grp in &mut g {
            let t = if grp.cls == b'E' {
                grp.z.min(left)
            } else {
                let c = ceil_log2(grp.r) as i32;
                if c <= left {
                    c
                } else {
                    0
                }
            };
            grp.t = t;
            grp.cb0 = cb;
            left -= t;
            cb += t;
            grp.left = if grp.cls == b'E' {
                grp.r >> t
            } else if grp.a_taken() {
                1
            } else {
                grp.r
            };
            rows *= grp.left as u128;
            if rows > (1u128 << WS_ROWS_MOST_LOG2) {
                return Err(Refusal::named("w-shape-mW"));
            }
        }
        let u = WsUnit {
            x,
            l,
            nlw,
            ncb: cb,
            g,
            rows: rows as u64,
            off: self.m0,
        };
        self.m0 += u.rows;
        if self.m0 > (1u64 << WS_ROWS_MOST_LOG2) {
            return Err(Refusal::named("w-shape-mW"));
        }
        self.u.push(u);
        Ok(())
    }

    /// `WsLay::build`: checks every number that reaches a shift, a loop or a product.
    pub fn build(&mut self, s: &WsShape, lk_w: u32) -> Result<()> {
        if !(1..=20).contains(&lk_w) {
            return Err(Refusal::named("w-shape-lk"));
        }
        if s.dd != 2048 && s.dd != 32 {
            return Err(Refusal::named("shape-D"));
        }
        if s.l == 0 || s.l > 4096 || s.moe.len() as u64 != s.l || s.moe_flag > 1 {
            return Err(Refusal::named("shape-words"));
        }
        for l in 0..s.l as usize {
            if (s.moe[l] != 0) != (s.moe_flag == 1 && (l & 1) != 0) {
                return Err(Refusal::named("internal-shape-moe"));
            }
        }
        for v in [s.d, s.dh, s.dkv, s.dq, s.f] {
            if v == 0 || v > (1u64 << 24) {
                return Err(Refusal::named("shape-words"));
            }
        }
        let any_moe = s.moe.iter().any(|&m| m != 0);
        if any_moe {
            for v in [s.fe, s.ne] {
                if v == 0 || v > (1u64 << 24) {
                    return Err(Refusal::named("shape-words"));
                }
            }
        }
        if s.eh > 1 || (s.eh == 1 && (s.v == 0 || s.v > (1u64 << 24))) {
            return Err(Refusal::named("shape-words"));
        }
        self.lk = lk_w as i32;
        self.m0 = 0;
        self.u.clear();
        for l in 0..s.l as u32 {
            self.add(0, l, 2, vec![Self::a_("hd", 64), Self::a_("cd", s.dh), Self::e_("kk", s.d, false)])?;
            self.add(1, l, 2, vec![Self::e_("kk", s.d, false), Self::e_("x", s.dkv, true)])?;
            self.add(2, l, 2, vec![Self::e_("kk", s.dq, false), Self::e_("x", s.d, true)])?;
            if s.moe[l as usize] == 0 {
                self.add(3, l, 2, vec![Self::e_("kk", s.d, false), Self::e_("x", s.f, true)])?;
                self.add(4, l, 2, vec![Self::e_("kk", s.d, false), Self::e_("x", s.f, true)])?;
                self.add(9, l, 2, vec![Self::e_("kk", s.f, false), Self::e_("x", s.d, true)])?;
            } else {
                self.add(5, l, 2, vec![Self::e_("kk", s.d, false), Self::e_("x", s.fe, true)])?;
                self.add(6, l, 2, vec![Self::e_("kk", s.d, false), Self::e_("x", s.fe, true)])?;
                self.add(
                    7,
                    l,
                    2,
                    vec![Self::e_("kk", s.d, false), Self::e_("e", s.ne, false), Self::e_("x", s.fe, true)],
                )?;
                self.add(
                    8,
                    l,
                    2,
                    vec![Self::e_("kk", s.d, false), Self::e_("e", s.ne, false), Self::e_("x", s.fe, true)],
                )?;
                self.add(9, l, 2, vec![Self::e_("kk", s.fe, false), Self::e_("x", s.d, true)])?;
                self.add(
                    10,
                    l,
                    2,
                    vec![Self::e_("kk", s.fe, false), Self::e_("e", s.ne, false), Self::e_("x", s.d, true)],
                )?;
                self.add(11, l, 2, vec![Self::e_("kk", s.d, false), Self::e_("x", s.ne, true)])?;
            }
        }
        if s.eh == 1 {
            self.add(12, s.l as u32, 4, vec![Self::a_("v", s.v), Self::e_("x", s.d, true)])?;
            self.add(13, s.l as u32, 2, vec![Self::a_("x", s.v), Self::e_("kk", s.d, false)])?;
        }
        self.m0 = (self.m0 + s.dd - 1) / s.dd * s.dd;
        if self.m0 > (1u64 << WS_ROWS_MOST_LOG2) {
            return Err(Refusal::named("w-shape-mW"));
        }
        Ok(())
    }
}

/// `wsEq1(p, x)`: `p x + (1 - p)(1 - x)`.
pub fn ws_eq1(p: E, x: E) -> E {
    p * x + (E::one() - p) * (E::one() - x)
}

/// A claim's factor for one index group (`struct WsFac`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WsFac {
    pub hv: Vec<E>,
    pub pt: Vec<E>,
    pub av: Vec<E>,
}

/// One claim (`struct WsClaim`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WsClaim {
    pub ui: u32,
    pub f: Vec<WsFac>,
}

/// A factor's part on the rows (`struct WsRowFac`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WsRowFac {
    pub hv: Vec<E>,
    pub pl: Vec<E>,
    pub av: Vec<E>,
}

/// What remains of a claim once the columns are fixed (`struct WsRecClaim`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WsRecClaim {
    pub ui: u32,
    pub ka: E,
    pub f: Vec<WsRowFac>,
}

/// `wsClaimShape`.
pub fn ws_claim_shape(lay: &WsLay, c: &WsClaim) -> Result<()> {
    if c.ui as usize >= lay.u.len() {
        return Err(Refusal::named("internal-claim-unit"));
    }
    let u = &lay.u[c.ui as usize];
    if c.f.len() != u.g.len() {
        return Err(Refusal::named("internal-claim-factors"));
    }
    for gi in 0..u.g.len() {
        let g = &u.g[gi];
        let x = &c.f[gi];
        let ok = if g.cls == b'E' {
            x.hv.len() as u64 == g.o && x.pt.len() as i32 == g.z && x.av.is_empty()
        } else {
            x.av.len() as u64 == g.r && x.hv.is_empty() && x.pt.is_empty()
        };
        if !ok {
            return Err(Refusal::named("internal-claim-factors"));
        }
    }
    Ok(())
}

/// `wsEpsT`: the multilinear extension of the claim's `eps_a` at `rm`.
pub fn ws_eps_t(lay: &WsLay, c: &WsClaim, rm: &[E]) -> E {
    let u = &lay.u[c.ui as usize];
    let lk = lay.lk;
    let x_at = |b: i32| rm[(lk - 1 - b) as usize];
    let mut p = E::one();
    for gi in 0..u.g.len() {
        let g = &u.g[gi];
        let x = &c.f[gi];
        if g.cls == b'E' {
            for i in 0..g.t {
                p = p * ws_eq1(x.pt[(g.z - 1 - g.taken_at(i)) as usize], x_at(g.cb0 + i));
            }
        } else if g.a_taken() {
            let mut zz = vec![E::zero(); g.t as usize];
            for s in 0..g.t {
                zz[s as usize] = x_at(g.cb0 + g.t - 1 - s);
            }
            let e = eq_tab(&zz, g.t as usize);
            let mut s = E::zero();
            for i in 0..g.r as usize {
                s = s + x.av[i] * e[i];
            }
            p = p * s;
        }
    }
    for b in u.ncb..lk {
        p = p * (E::one() - x_at(b));
    }
    p
}

/// `wsRowPart`.
pub fn ws_row_part(lay: &WsLay, c: &WsClaim, ka: E) -> WsRecClaim {
    let u = &lay.u[c.ui as usize];
    let mut r = WsRecClaim { ui: c.ui, ka, f: vec![WsRowFac::default(); u.g.len()] };
    for gi in 0..u.g.len() {
        let g = &u.g[gi];
        if g.cls == b'E' {
            r.f[gi].hv = c.f[gi].hv.clone();
            for b in (0..g.z).rev() {
                if !g.taken_bit(b) {
                    r.f[gi].pl.push(c.f[gi].pt[(g.z - 1 - b) as usize]);
                }
            }
        } else if !g.a_taken() {
            r.f[gi].av = c.f[gi].av.clone();
        }
    }
    r
}

/// `wsGammaAdd`: adds `wgt * ka * gamma_a[y]` to `gam[u.off + y]`.
pub fn ws_gamma_add(gam: &mut Vec<E>, lay: &WsLay, c: &WsRecClaim, wgt: E) -> Result<()> {
    let u = &lay.u[c.ui as usize];
    let mut v = vec![E::zero(); u.nlw as usize];
    {
        let mut s = wgt * c.ka;
        for item in &mut v {
            *item = s;
            s = e_scale(s, WS_SECOND_DIGIT as u64);
        }
    }
    for gi in (0..u.g.len()).rev() {
        let g = &u.g[gi];
        let x = &c.f[gi];
        let mut rf = vec![E::zero(); g.left as usize];
        if g.cls == b'E' {
            let zl = g.z - g.t;
            let e = eq_tab(&x.pl, zl as usize);
            for hi in 0..g.o as usize {
                for lo in 0..(1usize << zl) {
                    rf[(hi << zl) + lo] = x.hv[hi] * e[lo];
                }
            }
        } else if g.a_taken() {
            rf[0] = E::one();
        } else {
            for i in 0..g.r as usize {
                rf[i] = x.av[i];
            }
        }
        let mut n2 = vec![E::zero(); v.len() * rf.len()];
        for i in 0..v.len() {
            for q in 0..rf.len() {
                n2[i * rf.len() + q] = v[i] * rf[q];
            }
        }
        v = n2;
    }
    if v.len() as u64 != u.rows || u.off + u.rows > gam.len() as u64 {
        return Err(Refusal::named("internal-gamma-rows"));
    }
    for y in 0..u.rows as usize {
        gam[u.off as usize + y] = gam[u.off as usize + y] + v[y];
    }
    Ok(())
}

/// What remains after the merge (`struct WsForkOut`).
pub struct WsForkOut {
    pub merged: WsMerged,
    pub rec: Vec<WsRecClaim>,
}

/// `wsForkEnd`: runs the merge and sets each `rec[a].ka`.
pub fn ws_fork_end(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    lay: &WsLay,
    cl: &[WsClaim],
    sv: &[u32],
    calls: &mut HashCalls,
) -> Result<WsForkOut> {
    if cl.is_empty() || cl.len() > 4096 || sv.len() != cl.len() {
        return Err(Refusal::internal(&alloc::format!("{}internal-claim-count", f.g)));
    }
    for c in cl {
        ws_claim_shape(lay, c)?;
    }
    let (merged, rho) = ws_fork_merge(f, tr, slot, lay.lk, sv, calls)?;
    let mut rec = Vec::with_capacity(cl.len());
    for a in 0..cl.len() {
        rec.push(ws_row_part(lay, &cl[a], rho[a] * ws_eps_t(lay, &cl[a], &merged.rm)));
    }
    Ok(WsForkOut { merged, rec })
}
