//! The lookup argument by product trees and its helpers, ported from
//! `verifier/src/vf_lookup_argument.h` and `verifier/src/vf_lookup_helpers.h`.
//!
//! A group of calls (`Call`: `2^n` keys, a public table of `2^k` rows) runs as one lookup inside
//! the caller's sub-proof. The key side is one forest of `2^dT`-key trees; the table side is one
//! table with one vector of multiplicities per call. One masked sumcheck ([`Psc`]) runs per level.
//!
//! C++ `HForest` holds `Call*`; a Rust struct cannot point into its caller, so [`HForest`] keeps
//! the call metadata it needs and returns each call's `alpha` and `zk` in [`HForest::zk`]. The
//! caller that owns the `Call`s writes them back (`HTailF2::transcript` does).

use alloc::format;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::field::gl64;
use crate::hash::calls::HashCalls;
use crate::numbers::codes::ceil_log2;
use crate::refusal::{Refusal, Result};

use super::common::{eq_tab, order_default, Call};
use super::engine::{
    hand_down, power_of_two_at_least, read_product_level_rounds, Aff, HFork, Owed,
};
use super::packing::e_scale;
use super::sumcheck::{
    layer_slots, psc_begin, psc_ends, psc_row, round_in, sumcheck_slots, Psc, RoundForm,
};
use super::transcript::{tr_answer, tr_point, RoundName, Tr};

/// One piece of a lookup call (`struct HPiece`): a block of `Rp` rows by `Cp` columns that starts
/// at row `r0`, column `c0` of `trees[tree]`; `row` is the index of its virtual row. [`place_z`]
/// sets `CP`, `a` and `b`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HPiece {
    pub tree: i32,
    pub row: i32,
    pub r0: u64,
    pub rp: u64,
    pub c0: u64,
    pub cp: u64,
    /// `Cp` rounded up to a power of two.
    pub c_p: u64,
    pub off: u64,
    /// `ceil(log2 Rp)`.
    pub a: i32,
    /// `a + log2 CP`.
    pub b: i32,
}

/// The call with its pieces (`struct HCallZ`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HCallZ {
    pub c: Call,
    pub pc: Vec<HPiece>,
}

/// A functional: a weight vector `phi` of length `L` with its table in a committed vector `U`
/// (`struct HFun`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HFun {
    pub m: i32,
    pub l: u64,
    pub phi: Vec<E>,
    pub tree: u32,
    pub at: u64,
    pub name: String,
}

/// One group's lookup (`struct HForest`). The fields up to `owedJoin` follow the C++ order.
#[derive(Clone, Debug)]
pub struct HForest {
    /// The calls' names, in the caller's list order.
    pub names: Vec<String>,
    /// Each call's padding row value (`tauAt(t0)`).
    pub pad_values: Vec<u64>,
    pub nc: i32,
    pub d_t: i32,
    pub k_t: i32,
    pub nt: i32,
    pub r_k: i32,
    pub c_k: i32,
    pub iota: Vec<i32>,
    pub first: Vec<i32>,
    pub call_of: Vec<i32>,
    /// `pub[y]`, `y < NT`: the number of padding keys in tree `y`.
    pub pub_: Vec<u64>,
    pub theta: E,
    pub alpha: E,
    /// The product of `alpha - (padding key)` over all padding keys.
    pub a: E,
    /// Claims, in order: tie (31), key levels (v), table levels (d), bits (1).
    pub rows: Vec<Aff>,
    /// The table leaves' sumcheck.
    pub leaves: Psc,
    /// `alpha - 1 - (the table at zb[0])`.
    pub leaves_a: E,
    /// The slot of the planes' value at `zb[1]`.
    pub s_bit: u32,
    /// The key side's point.
    pub zx: Vec<E>,
    pub zy: Vec<E>,
    /// `e[c]`: the weight of call `c`'s trees at `zy`, in list order.
    pub e: Vec<E>,
    /// The hidden value of the key side's leaves at `(zx | zy)`.
    pub c_end: Aff,
    /// The points at which the planes are read.
    pub zb: [Vec<E>; 2],
    /// `tT[c]`: call `c`'s table at `zb[0]`'s last `k_c` coordinates of `t`.
    pub t_t: Vec<E>,
    /// Each call's `zk`, filled by [`forest_pad`].
    pub zk: Vec<Vec<E>>,
    pub owed_objects: Option<Rc<Owed>>,
    pub owed_planes: Option<Rc<Owed>>,
    pub owed_join: Option<Rc<Owed>>,
}

impl HForest {
    /// `HForest()`.
    pub fn new() -> Self {
        Self {
            names: Vec::new(),
            pad_values: Vec::new(),
            nc: 0,
            d_t: 0,
            k_t: 0,
            nt: 0,
            r_k: 0,
            c_k: 0,
            iota: Vec::new(),
            first: Vec::new(),
            call_of: Vec::new(),
            pub_: Vec::new(),
            theta: E::zero(),
            alpha: E::zero(),
            a: E::one(),
            rows: Vec::new(),
            leaves: Psc::default(),
            leaves_a: E::zero(),
            s_bit: 0,
            zx: Vec::new(),
            zy: Vec::new(),
            e: Vec::new(),
            c_end: Aff::default(),
            zb: [Vec::new(), Vec::new()],
            t_t: Vec::new(),
            zk: Vec::new(),
            owed_objects: None,
            owed_planes: None,
            owed_join: None,
        }
    }

    /// `HForest::v()`.
    pub fn v(&self) -> i32 {
        self.d_t + self.r_k
    }

    /// `HForest::d()`.
    pub fn d(&self) -> i32 {
        self.k_t + self.c_k
    }

    /// `HForest::b(y)`: which tree of its call.
    pub fn b(&self, y: u64) -> i32 {
        y as i32 - self.first[self.call_of[y as usize] as usize]
    }

    /// `HForest::emptyKeys()`.
    pub fn empty_keys(&self) -> u64 {
        ((1u64 << self.r_k) - self.nt as u64) << self.d_t
    }

    /// `HForest::padding()`.
    pub fn padding(&self) -> u64 {
        let mut s = self.empty_keys();
        for &x in &self.pub_ {
            s += x;
        }
        s
    }

    /// `HForest::padKey(c)`.
    pub fn pad_key(&self, c: i32) -> E {
        e_scale(E::one(), self.pad_values[c as usize])
            + e_scale(self.theta, c as u64)
    }

    /// `forestPubRun`, as a method so that `pub_` and the sizes can be borrowed together.
    pub fn pub_run(&mut self, c: i32, first: u64, count: u64) -> Result<()> {
        if self.pub_.len() != self.nt as usize || c < 0 || c as usize >= self.iota.len() {
            return Err(Refusal::named("internal-forest-pub"));
        }
        let n = 1u64 << (self.d_t + self.iota[c as usize]);
        let d = 1u64 << self.d_t;
        if first > n || count > n - first {
            return Err(Refusal::named("internal-forest-pub"));
        }
        let mut first = first;
        let mut count = count;
        while count != 0 {
            let b = first >> self.d_t;
            let take = count.min((b + 1) * d - first);
            self.pub_[(self.first[c as usize] as u64 + b) as usize] += take;
            first += take;
            count -= take;
        }
        Ok(())
    }
}

impl Default for HForest {
    fn default() -> Self {
        Self::new()
    }
}

/// `orderForestRange(mu, rK)`: the last key level's order of rounds.
pub fn order_forest_range(mu: i32, r_k: i32) -> Vec<u32> {
    let mut o = Vec::new();
    for v in [2, 1, 0, 5, 4, 3, 8, 7, 6] {
        o.push((r_k + v) as u32);
    }
    for v in (r_k + 9..mu).rev() {
        o.push(v as u32);
    }
    for v in (0..r_k).rev() {
        o.push(v as u32);
    }
    o
}

/// `forestShape`: a group's sizes and the checks on them. `lid` caps `dT`.
pub fn forest_shape(cl: &[Call], lid: i32) -> Result<HForest> {
    let mut h = HForest::new();
    for c in cl {
        if c.k < 5
            || c.k > 16
            || c.func < 0
            || c.func > 2
            || (c.t0 >> c.k) != 0
            || c.n > 62
            || c.n < 0
            || c.tau.as_ref().map_or(false, |t| t.len() != (1usize << c.k))
        {
            return Err(Refusal::named(&format!("shape-pt-words-{}", c.name)));
        }
        if let Some(tau) = &c.tau {
            for &x in tau {
                if x >= gl64::P {
                    return Err(Refusal::named(&format!("forest-row-value-{}", c.name)));
                }
            }
        }
        if c.n < 10 {
            return Err(Refusal::named("hid-call-floor"));
        }
        if c.kappa != 5 || !c.heavy.is_empty() {
            return Err(Refusal::named(&format!("hid-planes-{}", c.name)));
        }
    }
    let nc = cl.len() as i32;
    if !(1..=16).contains(&nc) {
        return Err(Refusal::named("forest-calls"));
    }
    h.nc = nc;
    while (1i32 << h.c_k) < nc {
        h.c_k += 1;
    }
    h.d_t = lid;
    for c in cl {
        h.d_t = h.d_t.min(c.n);
        h.k_t = h.k_t.max(c.k);
    }
    if h.d_t < 10 {
        return Err(Refusal::named("forest-depth"));
    }
    let mut nt = 0u64;
    h.iota = vec![0; nc as usize];
    for c in 0..nc as usize {
        h.iota[c] = cl[c].n - h.d_t;
        nt += 1u64 << h.iota[c];
    }
    if nt > 256 {
        return Err(Refusal::named("forest-trees"));
    }
    h.nt = nt as i32;
    while (1i32 << h.r_k) < h.nt {
        h.r_k += 1;
    }
    if h.v() >= 32 {
        return Err(Refusal::named("forest-keys"));
    }
    if ((1u128) << (h.d() + 32)) >= gl64::P as u128 {
        return Err(Refusal::named("no-wrap-pin-forest"));
    }
    let mut ord: Vec<usize> = (0..nc as usize).collect();
    ord.sort_by(|&a, &b| h.iota[b].cmp(&h.iota[a]));
    h.first = vec![0; nc as usize];
    h.call_of = vec![-1; h.nt as usize];
    let mut at = 0i32;
    for &c in &ord {
        h.first[c] = at;
        if at % (1i32 << h.iota[c]) != 0 {
            return Err(Refusal::named("internal-forest-place"));
        }
        for b in 0..(1i32 << h.iota[c]) {
            h.call_of[(at + b) as usize] = c as i32;
        }
        at += 1i32 << h.iota[c];
    }
    if at != h.nt {
        return Err(Refusal::named("internal-forest-place"));
    }
    h.names = cl.iter().map(|c| c.name.clone()).collect();
    h.pad_values = cl.iter().map(|c| c.tau_at(c.t0)).collect();
    Ok(h)
}

/// `forestPubRun`: adds `count` padding places of call `c`, from place `first`, to `pub`.
pub fn forest_pub_run(h: &HForest, pub_: &mut [u64], c: i32, first: u64, count: u64) -> Result<()> {
    if pub_.len() != h.nt as usize || c < 0 || c as usize >= h.iota.len() {
        return Err(Refusal::named("internal-forest-pub"));
    }
    let n = 1u64 << (h.d_t + h.iota[c as usize]);
    let d = 1u64 << h.d_t;
    if first > n || count > n - first {
        return Err(Refusal::named("internal-forest-pub"));
    }
    let mut first = first;
    let mut count = count;
    while count != 0 {
        let b = first >> h.d_t;
        let take = count.min((b + 1) * d - first);
        pub_[(h.first[c as usize] as u64 + b) as usize] += take;
        first += take;
        count -= take;
    }
    Ok(())
}

/// `forestPubAsk`: rejects counts of padding keys with more padding keys in a tree than places, or
/// with a call that is all padding.
pub fn forest_pub_ask(h: &HForest, names: &[String], pub_: &[u64], prefix: &str) -> Result<()> {
    if pub_.len() != h.nt as usize || names.len() != h.nc as usize {
        return Err(Refusal::named(&format!("{}internal-forest-pub", prefix)));
    }
    for &x in pub_ {
        if x > (1u64 << h.d_t) {
            return Err(Refusal::named("pt-pub-forest"));
        }
    }
    for c in 0..h.nc as usize {
        let mut padded = 0u64;
        for b in 0..(1i32 << h.iota[c]) {
            padded += pub_[(h.first[c] + b) as usize];
        }
        if padded >> (h.d_t + h.iota[c]) != 0 {
            return Err(Refusal::named(&format!("forest-only-padding-{}", names[c])));
        }
    }
    Ok(())
}

/// `forestElems`: the lookup's number of message slots.
pub fn forest_elems(h: &HForest) -> usize {
    let mut s = sumcheck_slots(RoundForm::Eq2, 0, 3, 3, 0) as usize
        + 30 * sumcheck_slots(RoundForm::Eq2, 0, 2, 3, 0) as usize;
    for mu in 0..h.v() {
        s += layer_slots(mu) as usize;
    }
    for l in 0..h.d() {
        s += layer_slots(5 + l) as usize;
    }
    s += 1 + 2 * h.d() as usize + 5;
    s + sumcheck_slots(RoundForm::Eq2, 5 + h.d(), 1, 2, 0) as usize
}

/// `forestPlan`: adds the lookup's rounds to the transcript's plan.
pub fn forest_plan(p: &mut crate::numbers::plan::Plan, where_: &str, h: &HForest) {
    let x = crate::numbers::blocks::LookupSize {
        v: h.v() as u32,
        d: h.d() as u32,
        mu: 5,
        shifted: h.nc > 1,
        ..Default::default()
    };
    crate::numbers::blocks::plan_lookup(p, where_, &x);
}

/// `forestLins`: the number of claims that [`forest_objects`] adds.
pub fn forest_lins(h: &HForest) -> usize {
    31 + h.v() as usize + h.d() as usize + 1
}

/// `forestDraws`: draws theta (several calls only) and alpha; computes `a`.
pub fn forest_draws(h: &mut HForest, tr: &mut Tr<'_, '_, '_, '_>, calls: &mut HashCalls) -> Result<()> {
    if h.nc > 1 {
        h.theta = tr_answer(tr, RoundName::LkpShift, calls)?;
    }
    h.alpha = tr_answer(tr, RoundName::Lkp, calls)?;
    h.a = (h.alpha - h.pad_key(0)).pow(h.empty_keys());
    for y in 0..h.nt as usize {
        h.a = h.a * (h.alpha - h.pad_key(h.call_of[y])).pow(h.pub_[y]);
    }
    Ok(())
}

/// `forestTie`: the tie and the point that joins the planes' roots. Returns `(sZ, rhoT, CT)`.
fn forest_tie(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    h: &mut HForest,
    calls: &mut HashCalls,
) -> Result<(u32, Vec<E>, Aff)> {
    let mut s_p = 0u32;
    let mut s_z = 0u32;
    let mut s_g = [0u32; 32];
    for j in 0..31 {
        let start = if j != 0 { Aff::slot(s_p) } else { Aff::constant(E::zero()) };
        let mut p = psc_begin(f, tr, slot, &start, calls)?;
        let mut at = psc_ends(f, tr, slot, &mut p, 3, if j != 0 { 2 } else { 3 }, calls)?;
        if j == 0 {
            s_z = at;
            at += 1;
        }
        s_p = at;
        s_g[j] = at + 1;
        let power = f.shown(s_p)? * f.shown(s_p)? * f.shown(s_g[j])?;
        let s0 = if j != 0 { power } else { f.shown(s_z)? - h.a * power };
        h.rows.push(psc_row(f, &mut p, s0, &Aff::default())?);
    }
    s_g[31] = s_p;
    // The planes' 32 roots are the table side's top level.
    let by_variable = tr_point(tr, RoundName::LkpPlanes, 5, calls)?;
    let rho_t: Vec<E> = by_variable.iter().rev().copied().collect();
    let ej = eq_tab(&rho_t, 5);
    let mut ct = Aff::default();
    for j in 0..32 {
        ct.add(&Aff::slot(s_g[j]), ej[j]);
    }
    Ok((s_z, rho_t, ct))
}

/// `forestPad`: runs the lookup's messages. Sets each call's `alpha` and `zk` in the result.
pub fn forest_pad(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    cl: &[Call],
    pub_in: &[u64],
    slot: &mut u32,
    lid: i32,
    calls: &mut HashCalls,
) -> Result<HForest> {
    let mut h = forest_shape(cl, lid)?;
    let (nc, d_t, k_t, r_k, c_k) = (h.nc, h.d_t, h.k_t, h.r_k, h.c_k);
    let (v, d, m) = (h.v(), h.d(), 5 + h.d());
    let names = h.names.clone();
    forest_pub_ask(&h, &names, pub_in, &f.g)?;
    h.pub_ = pub_in.to_vec();
    let slot0 = *slot;
    h.owed_objects = Some(f.owe("look-up-mask-claims"));
    h.owed_planes = Some(f.owe("look-up-plane-claims"));
    h.owed_join = Some(f.owe("look-up-join"));
    forest_draws(&mut h, tr, calls)?;
    let (s_z, mut rho_t, mut ct) = forest_tie(f, tr, slot, &mut h, calls)?;
    {
        let mut rho: Vec<E> = Vec::new();
        let mut c = Aff::slot(s_z);
        for mu in 0..v {
            let order = if mu == v - 1 {
                order_forest_range(mu, r_k)
            } else {
                order_default(mu as usize)
            };
            let o = read_product_level_rounds(f, tr, slot, mu as usize, &rho, &c, &order, calls)?;
            hand_down(&o, &mut rho, &mut c);
            h.rows.push(o.row);
        }
        h.zx = rho[..d_t as usize].to_vec();
        h.zy = rho[d_t as usize..].to_vec();
        h.c_end = c;
    }
    for l in 0..d {
        let order = order_default((5 + l) as usize);
        let o = read_product_level_rounds(f, tr, slot, (5 + l) as usize, &rho_t, &ct, &order, calls)?;
        hand_down(&o, &mut rho_t, &mut ct);
        h.rows.push(o.row);
    }
    if rho_t.len() != m as usize {
        return Err(Refusal::internal(&format!("{}internal-forest-point", f.g)));
    }
    // The table leaves are `1 + b (alpha - 1 - row)`: affine in the planes, so no value is shown.
    h.leaves = psc_begin(f, tr, slot, &ct, calls)?;
    h.zb[0] = vec![E::zero(); m as usize];
    for j in 0..m as usize {
        h.zb[0][j] = round_in(
            f,
            tr,
            slot,
            RoundForm::Eq,
            &mut h.leaves,
            rho_t[j],
            if (j as i32) < d { 2 } else { 1 },
            calls,
        )?;
    }
    // The bits are bits: `sum eq(point, .) (b^2 - b) = 0` at a fresh point.
    {
        let by_variable = tr_point(tr, RoundName::Zero, m as usize, calls)?;
        let r5: Vec<E> = by_variable.iter().rev().copied().collect();
        let mut p = psc_begin(f, tr, slot, &Aff::constant(E::zero()), calls)?;
        h.zb[1] = vec![E::zero(); m as usize];
        for j in 0..m as usize {
            h.zb[1][j] = round_in(f, tr, slot, RoundForm::Eq2, &mut p, r5[j], 0, calls)?;
        }
        h.s_bit = psc_ends(f, tr, slot, &mut p, 2, 1, calls)?;
        let s0 = f.shown(h.s_bit)? * f.shown(h.s_bit)? - f.shown(h.s_bit)?;
        h.rows.push(psc_row(f, &mut p, s0, &Aff::default())?);
    }
    if *slot != slot0 + forest_elems(&h) as u32 || h.rows.len() != forest_lins(&h) {
        return Err(Refusal::internal(&format!("{}internal-slot-count", f.g)));
    }
    // `e_c = eq(zy's first hi coordinates, the top hi bits of first[c])`, `zk_c = (rest of zy | zx)`.
    h.e = vec![E::zero(); nc as usize];
    h.t_t = vec![E::zero(); nc as usize];
    h.zk = vec![Vec::new(); nc as usize];
    for c in 0..nc as usize {
        let k = &cl[c];
        let hi = r_k - h.iota[c];
        if hi < 0 {
            return Err(Refusal::internal(&format!("{}internal-forest-place", f.g)));
        }
        let pre = (h.first[c] as u64) >> h.iota[c];
        let mut e = E::one();
        for i in 0..hi {
            let bit = (pre >> (hi - 1 - i)) & 1 != 0;
            e = e * if bit { h.zy[i as usize] } else { E::one() - h.zy[i as usize] };
        }
        h.e[c] = e;
        let mut zk: Vec<E> = h.zy[hi as usize..].to_vec();
        zk.extend_from_slice(&h.zx);
        if zk.len() != k.n as usize {
            return Err(Refusal::internal(&format!("{}internal-forest-point", f.g)));
        }
        h.zk[c] = zk;
        let u = &h.zb[0][(k_t - k.k) as usize..];
        let mut tt = E::zero();
        match &k.tau {
            None => {
                for i in 0..k.k as usize {
                    tt = tt + e_scale(u[i], 1u64 << (k.k as usize - 1 - i));
                }
            }
            Some(tau) => {
                let et = eq_tab(u, k.k as usize);
                for t in 0..et.len() {
                    tt = tt + e_scale(et[t], tau[t]);
                }
            }
        }
        h.t_t[c] = tt;
    }
    {
        let ec = eq_tab(&h.zb[0][k_t as usize..], c_k as usize);
        let mut row = E::zero();
        for c in 0..(1usize << c_k) {
            let of = c.min(nc as usize - 1);
            row = row + ec[c] * (h.t_t[of] + e_scale(h.theta, of as u64));
        }
        h.leaves_a = h.alpha - E::one() - row;
    }
    Ok(h)
}

/// `forestObjects`: adds the claims on mask entries only.
pub fn forest_objects(f: &mut HFork, h: &HForest) -> Result<()> {
    let owed = h.owed_objects.as_ref().ok_or_else(|| Refusal::named("internal-forest-no-proof-read"))?;
    for row in &h.rows {
        f.lin(row)?;
    }
    owed.added.set(true);
    Ok(())
}

/// `forestPaddingLaid`: the two descriptions of the padding must agree.
pub fn forest_padding_laid(h: &HForest, laid: &[u64]) -> Result<()> {
    if laid != h.pub_.as_slice() {
        return Err(Refusal::named("internal-forest-padding-places"));
    }
    Ok(())
}

/// `forestPlanesAdded`.
pub fn forest_planes_added(h: &HForest) -> Result<()> {
    let owed = h.owed_planes.as_ref().ok_or_else(|| Refusal::named("internal-forest-no-proof-read"))?;
    owed.added.set(true);
    Ok(())
}

/// `forestJoinAdded`.
pub fn forest_join_added(h: &HForest) -> Result<()> {
    let owed = h.owed_join.as_ref().ok_or_else(|| Refusal::named("internal-forest-no-proof-read"))?;
    owed.added.set(true);
    Ok(())
}

/// `forestJoin`: the claim on the calls' key vectors.
pub fn forest_join(h: &HForest, kf: &[Aff]) -> Result<Aff> {
    if kf.len() != h.nc as usize || h.e.len() != h.nc as usize {
        return Err(Refusal::named("internal-forest-join"));
    }
    forest_join_added(h)?;
    let mut f = Aff::default();
    for c in 0..kf.len() {
        f.add(
            &(Aff::constant(h.alpha - e_scale(h.theta, c as u64)) - kf[c].clone()),
            h.e[c],
        );
    }
    let ey = eq_tab(&h.zy, h.r_k as usize);
    for y in h.nt as usize..(1usize << h.r_k) {
        f.c = f.c + ey[y] * (h.alpha - h.pad_key(0));
    }
    Ok(f - h.c_end.clone())
}

/// `forestPlaneCols`: the number of columns of the planes' matrix of `2^lm` rows.
pub fn forest_plane_cols(h: &HForest, lm: i32) -> Result<u64> {
    if lm < 5 || lm > h.k_t + 5 {
        return Err(Refusal::named("forest-planes"));
    }
    Ok((h.nc as u64) << (h.k_t + 5 - lm))
}

/// `forestPlaneClaims`: the three claims that read the planes. `tb(e, col)` and `tp(col)` are the
/// caller's forms on the planes' matrix.
pub fn forest_plane_claims<FB, FP>(
    f: &mut HFork,
    h: &mut HForest,
    lm: i32,
    tb: FB,
    tp: FP,
) -> Result<Vec<Aff>>
where
    FB: Fn(i32, u64) -> Aff,
    FP: Fn(u64) -> Aff,
{
    let _ = forest_plane_cols(h, lm)?;
    let w = h.k_t + 5 - lm;
    let mut at = [Aff::default(), Aff::default()];
    for e in 0..2i32 {
        let ec = eq_tab(&h.zb[e as usize][h.k_t as usize..], h.c_k as usize);
        let et = eq_tab(&h.zb[e as usize], w as usize);
        for c in 0..h.nc as u64 {
            for th in 0..(1u64 << w) {
                at[e as usize].add(&tb(e, (c << w) + th), ec[c as usize] * et[th as usize]);
            }
        }
    }
    let mut f0 = Aff::constant(
        E::zero() - e_scale(E::one(), (1u64 << h.v()) - h.padding()),
    );
    for col in 0..((h.nc as u64) << w) {
        f0.add(&tp(col), E::one());
    }
    let s_bit = h.s_bit;
    let leaves_a = h.leaves_a;
    let c0 = psc_row(f, &mut h.leaves, E::one(), &(at[0].clone() * leaves_a))?;
    Ok(vec![c0, Aff::slot(s_bit) - at[1].clone(), f0])
}

/// `forestPlaneLins`: adds the three claims that read the planes and marks them.
pub fn forest_plane_lins<FB, FP>(
    f: &mut HFork,
    h: &mut HForest,
    lm: i32,
    tb: FB,
    tp: FP,
) -> Result<()>
where
    FB: Fn(i32, u64) -> Aff,
    FP: Fn(u64) -> Aff,
{
    let claims = forest_plane_claims(f, h, lm, tb, tp)?;
    if claims.len() != 3 {
        return Err(Refusal::named("internal-forest-join"));
    }
    for c in &claims {
        f.lin(c)?;
    }
    forest_planes_added(h)
}

/// `forestPhiB`: the row weights `phiB_e`.
pub fn forest_phi_b(h: &HForest, lm: i32, e: usize) -> Result<Vec<E>> {
    let _ = forest_plane_cols(h, lm)?;
    let mut z: Vec<E> = h.zb[e][(h.k_t + 5 - lm) as usize..h.k_t as usize].to_vec();
    z.extend_from_slice(&h.zb[e][(h.k_t + h.c_k) as usize..]);
    Ok(eq_tab(&z, lm as usize))
}

/// `forestPhiP`: the row weights `phiP`.
pub fn forest_phi_p(lm: i32) -> Vec<E> {
    let mut p = vec![E::zero(); 1usize << lm];
    for r in 0..p.len() {
        p[r] = e_scale(E::one(), 1u64 << (r & 31));
    }
    p
}

/// `uEnt(F, t, x)`: the affine form for element `x` of a table of `Kw` columns, stored in virtual
/// row `floor(x / Kw)` of `trees[t]`.
pub fn u_ent(f: &HFork, t: u32, x: u64) -> Result<Aff> {
    let kw = f.trees[t as usize].k;
    if (x / kw) >> 32 != 0 {
        return Err(Refusal::internal(&format!("{}internal-L-row", f.g)));
    }
    Ok(Aff::ent(t, (x / kw) as u32, x % kw))
}

/// `placeZ`: places the pieces, largest first, so that `2^b` divides `off`, and fills in the call.
pub fn place_z(z: &mut HCallZ, name: &str, k: i32, lid: i32) -> Result<()> {
    for p in &mut z.pc {
        p.a = ceil_log2(p.rp) as i32;
        p.c_p = power_of_two_at_least(p.cp);
        p.b = p.a + ceil_log2(p.c_p) as i32;
    }
    let mut ord: Vec<usize> = (0..z.pc.len()).collect();
    ord.sort_by(|&x, &y| z.pc[y].b.cmp(&z.pc[x].b));
    let mut off = 0u64;
    for i in ord {
        z.pc[i].off = off;
        off += 1u64 << z.pc[i].b;
    }
    let c = &mut z.c;
    c.name = String::from(name);
    c.k = k;
    c.kappa = 5;
    c.func = 0;
    c.t0 = 0;
    c.n = if ceil_log2(off) < 10 { 10 } else { ceil_log2(off) as i32 };
    c.iota = if c.n > lid { c.n - lid } else { 0 };
    // pub counts the padding keys: in each piece, columns `Cp .. CP - 1` of rows `0 .. Rp - 1`,
    // and all keys after the last piece.
    let big_i = c.i_count();
    let n = 1u64 << c.n;
    let mut pub_ = vec![0u64; big_i as usize];
    let pad_run = |first: u64, count: u64, pub_: &mut Vec<u64>| {
        let whole = count / big_i;
        for b in 0..big_i as usize {
            pub_[b] += whole;
        }
        let mut i = first + whole * big_i;
        while i < first + count {
            pub_[(i & (big_i - 1)) as usize] += 1;
            i += 1;
        }
    };
    for p in &z.pc {
        if p.cp < p.c_p {
            for rr in 0..p.rp {
                pad_run(p.off + rr * p.c_p + p.cp, p.c_p - p.cp, &mut pub_);
            }
        }
    }
    if off < n {
        pad_run(off, n - off, &mut pub_);
    }
    z.c.public = pub_;
    Ok(())
}

/// The layer sub-proof's batched sumcheck (`struct HStack`): `lam` rounds with no equality
/// factor, and their challenges.
#[derive(Clone, Debug, Default)]
pub struct HStack {
    pub lam: i32,
    pub rs: Vec<E>,
    pub p: Psc,
}

/// `stackRounds`: reads the `lam` rounds, each of degree 2, from bit `lam - 1` down.
pub fn stack_rounds(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    st: &mut HStack,
    calls: &mut HashCalls,
) -> Result<()> {
    st.rs = vec![E::zero(); st.lam as usize];
    for v in (0..st.lam).rev() {
        st.rs[v as usize] =
            round_in(f, tr, slot, RoundForm::Sum2, &mut st.p, E::zero(), 0, calls)?;
    }
    Ok(())
}

/// `eqLowAt` for a caller that has the point already (`eq_low_at` lives in [`super::segment`]).
pub fn eq_low_entry(rs: &[E], lo: i32, hi: i32, c: u64) -> Result<E> {
    super::segment::eq_low_at(rs, lo, hi, c)
}
