//! The arrays and claims that a sub-proof's segment shares, ported from the parts of
//! `verifier/src/vf_subproof_segment.h` that the sub-proof checks use without a frame:
//! [`N2`], [`Tail2`], `t2AddN`, `t2AddP`, `t2Plan`, `t2FillL`, [`Run2`], `t2Lin` and [`EqRun`].
//!
//! The frame side of the header (`LinkCtx`, `currentSegment`, `rootInH`, `t2Batch`, `doorH`,
//! `rowWeights`) receives and closes the request's segments; that wiring belongs to the sub-proof layer, so this module
//! stops at the equation's weights. `t2Lin`'s C++ test support (`valuesF`) is omitted, as in
//! [`super::engine`].

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::refusal::{Refusal, Result};

use super::engine::{Aff, HFork, HTree, TreeKind};
use super::packing::ShP;

/// What the list keeps of an array beside its [`HTree`] (`struct N2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct N2 {
    /// 1 (base field) or `CE` (the field E).
    pub ec: u32,
    /// `1 +` the other sub-proofs that read the array.
    pub a: u32,
    /// An earlier sub-proof, the owner, has committed to the array.
    pub foreign: bool,
    /// No function sets it; `doorH` ends without a verdict if it is set.
    pub outside: bool,
    /// A symbol tree: the array of the symbols of one matrix of the range check.
    pub p: bool,
    pub shape: ShP,
}

impl Default for N2 {
    fn default() -> Self {
        Self { ec: 1, a: 1, foreign: false, outside: false, p: false, shape: ShP::default() }
    }
}

/// The list of arrays (`struct Tail2`).
#[derive(Clone, Debug, Default)]
pub struct Tail2 {
    /// `HTailF2::addTreesF` sets it before the first array.
    pub link: bool,
    pub nt: Vec<N2>,
    /// The slots that the sub-proof's messages have taken.
    pub used: u32,
    pub planned: bool,
    pub walked: bool,
}

fn order(f: &HFork) -> Refusal {
    Refusal::internal(&alloc::format!("{}internal-t2-order", f.g))
}

/// `t2AddN`: adds an array of `r` rows and `k` columns with `nv` virtual rows. Returns its index.
pub fn t2_add_n(
    f: &mut HFork,
    t: &mut Tail2,
    name: &str,
    r: u64,
    k: u64,
    ec: u32,
    a: u32,
    foreign: bool,
    nv: u32,
) -> Result<u32> {
    if !t.link || t.planned || f.trees.len() != t.nt.len() {
        return Err(order(f));
    }
    f.trees.push(HTree {
        name: String::from(name),
        kind: TreeKind::N,
        r,
        k,
        root: false,
        owner: !foreign,
        rows: vec![Default::default(); nv as usize],
    });
    t.nt.push(N2 { ec, a, foreign, ..N2::default() });
    Ok(f.trees.len() as u32 - 1)
}

/// `t2AddP`: adds the symbol tree of one matrix of the range check.
pub fn t2_add_p(
    f: &mut HFork,
    t: &mut Tail2,
    name: &str,
    m: u64,
    k: u64,
    w: u32,
    a: u32,
    foreign: bool,
) -> Result<u32> {
    if !t.link || t.planned || f.trees.len() != t.nt.len() {
        return Err(order(f));
    }
    if w != 0 {
        return Err(Refusal::named("plan-w-zero"));
    }
    let mut n = N2 { ec: 1, a, foreign, p: true, ..N2::default() };
    n.shape.m = m;
    n.shape.k = k;
    n.shape.m_s = (m + 2) / 3;
    n.shape.j = 1;
    n.shape.c_j = 0;
    n.shape.r = n.shape.m_s;
    n.shape.rr = n.shape.m_s;
    n.shape.rd = 0;
    n.shape.a_x = crate::numbers::codes::ceil_log2(n.shape.m_s) as i32;
    n.shape.k1 = k;
    n.shape.kc = k;
    n.shape.a = a;
    f.trees.push(HTree {
        name: String::from(name),
        kind: TreeKind::P,
        r: n.shape.rr,
        k: n.shape.kc,
        root: false,
        owner: !foreign,
        rows: vec![Default::default()],
    });
    t.nt.push(n);
    Ok(f.trees.len() as u32 - 1)
}

/// `t2Plan`: closes the list to further arrays.
pub fn t2_plan(f: &mut HFork, t: &mut Tail2) -> Result<()> {
    if !t.link || t.planned || f.trees.len() != t.nt.len() {
        return Err(order(f));
    }
    t.planned = true;
    Ok(())
}

/// `t2FillL`: gives each virtual row of the listed arrays `K` column weights, all zero, unless it
/// has `K` already.
pub fn t2_fill_l(f: &mut HFork, t: &Tail2) {
    for ti in 0..t.nt.len() {
        let k = f.trees[ti].k as usize;
        for r in &mut f.trees[ti].rows {
            if r.l.len() != k {
                r.l = vec![E::zero(); k];
            }
        }
    }
}

/// `t2Batch`'s state changes, for a caller that has already drawn the batching element with
/// `trBatchOpen` (the draw must be the sub-proof's last transcript operation; the frame gate
/// enforces that).
pub fn t2_batch(f: &mut HFork, t: &mut Tail2, theta: E, used: u32) -> Result<()> {
    if !t.planned || used != f.ns {
        return Err(Refusal::internal(&alloc::format!("{}internal-slot-count", f.g)));
    }
    t2_fill_l(f, t);
    t.used = used;
    f.batch_by(theta)?;
    if f.plan_claims == 0 {
        return Err(Refusal::internal(&alloc::format!("{}internal-f-draws", f.g)));
    }
    f.kap_map = vec![false; f.plan_claims as usize];
    Ok(())
}

/// One run of entries in a linear claim (`struct Run2`): `coef * w[w0 + i]` on column
/// `first + i` of a virtual row, for `i < n`.
pub struct Run2<'a> {
    pub tree: u32,
    pub row: u32,
    pub first: u64,
    pub coef: E,
    pub w: Option<&'a [E]>,
    pub w0: u64,
    pub n: u64,
}

impl<'a> Default for Run2<'a> {
    fn default() -> Self {
        Self { tree: 0, row: 0, first: 0, coef: E::one(), w: None, w0: 0, n: 0 }
    }
}

/// `t2Lin`: adds the claim
/// `a + sum over runs and i < n of coef * w[w0 + i] * entry(tree, row, first + i) = 0`.
pub fn t2_lin(f: &mut HFork, a: &Aff, runs: &[Run2<'_>]) -> Result<()> {
    let k = f.kap()?;
    f.push(k, a)?;
    for r in runs {
        let w = match r.w {
            Some(w) => w,
            None => {
                return Err(Refusal::internal(&alloc::format!("{}internal-L-index", f.g)));
            }
        };
        if r.w0 > w.len() as u64 || r.n > w.len() as u64 - r.w0 {
            return Err(Refusal::internal(&alloc::format!("{}internal-L-index", f.g)));
        }
        if r.tree as usize >= f.trees.len() || r.row as usize >= f.trees[r.tree as usize].rows.len()
        {
            return Err(Refusal::internal(&alloc::format!("{}internal-L-row", f.g)));
        }
        let row = &mut f.trees[r.tree as usize].rows[r.row as usize];
        let l = &mut row.l;
        if r.first < row.l0
            || r.first - row.l0 > l.len() as u64
            || r.n > l.len() as u64 - (r.first - row.l0)
        {
            return Err(Refusal::internal(&alloc::format!("{}internal-L-index", f.g)));
        }
        let kc = k * r.coef;
        let start = (r.first - row.l0) as usize;
        for i in 0..r.n as usize {
            let x = w[r.w0 as usize + i];
            if !x.is_zero() {
                l[start + i] = l[start + i] + kc * x;
            }
        }
    }
    Ok(())
}

/// `EqRun`: gives `lead * eq(zp, idx)` at consecutive indices, the equality polynomial of `zp`
/// and the `n` low bits of `idx`.
pub struct EqRun {
    z: Vec<E>,
    n: i32,
    idx: u64,
    pre: Vec<E>,
    om: Vec<E>,
}

impl EqRun {
    /// The C++ constructor `EqRun(zp, n, idx, lead = eO())`.
    pub fn new(zp: &[E], n: i32, idx: u64, lead: E) -> Self {
        let mut e = Self {
            z: zp.to_vec(),
            n,
            idx,
            pre: vec![E::zero(); n as usize + 1],
            om: vec![E::zero(); n as usize],
        };
        for v in 0..n as usize {
            e.om[v] = E::one() - e.z[v];
        }
        e.pre[0] = lead;
        e.from(0);
        e
    }

    fn from(&mut self, v0: i32) {
        for v in v0..self.n {
            let bit = (self.idx >> (self.n - 1 - v)) & 1 != 0;
            self.pre[v as usize + 1] = self.pre[v as usize]
                * if bit { self.z[v as usize] } else { self.om[v as usize] };
        }
    }

    /// `at()`.
    pub fn at(&self) -> E {
        self.pre[self.n as usize]
    }

    /// `next()`.
    pub fn next(&mut self) {
        let j = 63 - (self.idx ^ self.idx.wrapping_add(1)).leading_zeros() as i32;
        self.idx = self.idx.wrapping_add(1);
        self.from(if j >= self.n { 0 } else { self.n - 1 - j });
    }
}

/// `eqLow(rs, lo, hi)`: the equality table over bits `lo .. hi - 1`, with `rs[v]` the coordinate
/// of bit `v`. `eqTab` expects coordinate 0 to be the top bit, so the coordinates are passed from
/// the top bit down.
pub fn eq_low(rs: &[E], lo: i32, hi: i32) -> Vec<E> {
    let mut z = Vec::with_capacity((hi - lo) as usize);
    for v in (lo..hi).rev() {
        z.push(rs[v as usize]);
    }
    super::common::eq_tab(&z, (hi - lo) as usize)
}

/// `eqLowAt(rs, lo, hi, c)`: entry `c` of [`eq_low`].
pub fn eq_low_at(rs: &[E], lo: i32, hi: i32, c: u64) -> Result<E> {
    let mut z = Vec::with_capacity((hi - lo) as usize);
    for v in (lo..hi).rev() {
        z.push(rs[v as usize]);
    }
    super::common::eq_one(&z, hi - lo, c)
}
