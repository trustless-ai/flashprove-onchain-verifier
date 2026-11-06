//! The sub-proof engine, ported from `verifier/src/vf_subproof_engine.h`.
//!
//! A sub-proof argues one part of the forward pass. Its hidden values are shown as
//! `value + factor * (entry of the committed mask row)`; a claim is an affine form ([`Aff`]) that
//! must be 0. `HFork` batches the claims into one equation; the C++ code passes that equation to
//! `ChainCheck`, which tests it at the end of the segment (`vf_subproof_segment.h`). That wiring
//! belongs to the sub-proof layer; here the engine keeps the equation and the values it is built from.
//!
//! C++ `refuse()` becomes a [`Refusal`] value. Every rejection name that C++ builds by appending
//! to `HFork::G_` keeps that prefix here. The prover-side test support of the C++ header
//! (`valuesF`, `judged`, `judgeAll`, `take`, `valueOf`, `TestProverValues`) is for the C++ test
//! harness `verifier/tests/claims_report.h`; no decision of the verifier reads it, so this port
//! leaves it out.

use alloc::format;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::Cell;

use crate::field::ext::E;
use crate::refusal::{Refusal, Result};

use super::sumcheck::{psc_begin, psc_ends, psc_row};
use super::transcript::{tr_answer, tr_read, RoundName, Tr};

/// The smallest power of two `>= v`. C++ requires `v <= 2^63`; for a larger value the C++ loop
/// never ends, so this port asserts it in debug builds and leaves the wrap in release.
pub fn power_of_two_at_least(v: u64) -> u64 {
    let mut p = 1u64;
    while p < v {
        p <<= 1;
    }
    p
}

/// One virtual row of an array (`struct HRow`): the vector `sum_r coef[r] * row r`. `l` is the
/// one equation's coefficients on its columns, `l0` the first column of the window.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HRow {
    pub coef: Vec<E>,
    pub l: Vec<E>,
    pub l0: u64,
    /// The C++ `rowForm`: `coef` is a product over the bits of the row number.
    pub row_form: bool,
    /// The C++ `rowOnes`: every row weight is 1.
    pub row_ones: bool,
    /// The C++ `rowPoint`: `coef[rowFirst + r] = eq(rowPoint, r)`.
    pub row_point: Vec<E>,
    /// The C++ `rowLo` / `rowHi`: `coef[r] = prod_t (bit t of r ? rowHi[t] : rowLo[t])`.
    pub row_lo: Vec<E>,
    pub row_hi: Vec<E>,
    pub row_first: u64,
}

/// `HTree::kind`: `'N'` is a plain array, `'P'` the symbol array of a matrix of the smallness test.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum TreeKind {
    #[default]
    N,
    P,
}

/// An array that a sub-proof's claims read (`struct HTree`).
///
/// C++ keeps `const u32 *root` as a "committed" mark; nothing reads the digest through it, so this
/// port keeps a bool. `owner` says that this sub-proof commits to the array.
#[derive(Clone, Debug, Default)]
pub struct HTree {
    pub name: String,
    pub kind: TreeKind,
    pub r: u64,
    pub k: u64,
    pub root: bool,
    pub owner: bool,
    pub rows: Vec<HRow>,
}

/// One term of an affine form: `coef * (entry idx of row `row` of tree `tree`)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ent {
    pub tree: u32,
    pub row: u32,
    pub idx: u64,
    pub coef: E,
}

impl Default for Ent {
    fn default() -> Self {
        Self { tree: 0, row: 0, idx: 0, coef: E::zero() }
    }
}

/// An affine form: `sum_e coef * entry + sum_s weight * (hidden value of slot s) + c`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Aff {
    pub e: Vec<Ent>,
    pub s: Vec<(u32, E)>,
    pub c: E,
}

impl Aff {
    /// `affC(v)`.
    pub fn constant(v: E) -> Self {
        Self { e: Vec::new(), s: Vec::new(), c: v }
    }

    /// `affSlot(j)`.
    pub fn slot(j: u32) -> Self {
        Self { e: Vec::new(), s: vec![(j, E::one())], c: E::zero() }
    }

    /// `affEnt(tree, row, idx)`.
    pub fn ent(tree: u32, row: u32, idx: u64) -> Self {
        Self {
            e: vec![Ent { tree, row, idx, coef: E::one() }],
            s: Vec::new(),
            c: E::zero(),
        }
    }

    /// `affAdd(a, b, k)`: `self += k * b`.
    pub fn add(&mut self, b: &Aff, k: E) {
        for x in &b.e {
            let mut y = *x;
            y.coef = x.coef * k;
            self.e.push(y);
        }
        for x in &b.s {
            self.s.push((x.0, x.1 * k));
        }
        self.c = self.c + b.c * k;
    }
}

impl core::ops::Add for Aff {
    type Output = Aff;
    fn add(mut self, b: Aff) -> Aff {
        Aff::add(&mut self, &b, E::one());
        self
    }
}

impl core::ops::Sub for Aff {
    type Output = Aff;
    fn sub(mut self, b: Aff) -> Aff {
        Aff::add(&mut self, &b, E::zero() - E::one());
        self
    }
}

impl core::ops::Mul<E> for Aff {
    type Output = Aff;
    fn mul(self, k: E) -> Aff {
        let mut r = Aff::default();
        r.add(&self, k);
        r
    }
}

/// A claim that a function leaves for its caller to add (`HFork::Owed`). The `added` flag is
/// `Cell` so that the marks can be set through a shared reference, as the C++ `shared_ptr` allows.
#[derive(Debug)]
pub struct Owed {
    pub what: String,
    pub added: Cell<bool>,
}

/// One sub-proof's state (`struct HFork`).
#[derive(Clone, Debug, Default)]
pub struct HFork {
    /// `G_`: the prefix of the sub-proof's rejection names.
    pub g: String,
    pub trees: Vec<HTree>,
    pub ns: u32,
    /// The hidden value of slot `j` is `vp[j] - mf[j] * (entry j of the mask row)`.
    pub vp: Vec<E>,
    pub mf: Vec<E>,
    /// The one equation's coefficient on each slot.
    pub ls: Vec<E>,
    pub c0: E,
    pub n_claim: u32,
    /// `gotF`: slot `j` has a value.
    pub got: Vec<bool>,
    pub theta: E,
    pub theta_drawn: bool,
    /// The planned number of claims (`HPlan2::nLin`).
    pub plan_claims: u32,
    /// `kapMapF`: slot `c` has taken its batching coefficient.
    pub kap_map: Vec<bool>,
    /// `doorShutF`: no further claim may be added.
    pub door_shut: bool,
    pub owed: Vec<Rc<Owed>>,
}

impl HFork {
    fn named(&self, suffix: &str) -> Refusal {
        Refusal::internal(&format!("{}internal-{}", self.g, suffix))
    }

    /// `rootTaken(t, w)`: marks the tree as committed.
    pub fn root_taken(&mut self, t: usize) {
        self.trees[t].root = true;
    }

    /// `slots(n)`: sets up `n` slots without values.
    pub fn slots(&mut self, n: u32) {
        self.ns = n;
        self.vp = vec![E::zero(); n as usize];
        self.mf = vec![E::zero(); n as usize];
        self.ls = vec![E::zero(); n as usize];
        self.got = vec![false; n as usize];
    }

    /// `hide(j, shownScalar, factor)`.
    pub fn hide(&mut self, j: u32, shown_scalar: E, factor: E) -> Result<()> {
        if j >= self.ns || self.got.len() != self.ns as usize {
            return Err(self.named("slot-marks"));
        }
        if self.got[j as usize] {
            return Err(self.named("slot-twice"));
        }
        self.got[j as usize] = true;
        self.vp[j as usize] = shown_scalar;
        self.mf[j as usize] = factor;
        Ok(())
    }

    /// `shown(j)`.
    pub fn shown(&self, j: u32) -> Result<E> {
        if j >= self.ns || !self.got[j as usize] {
            return Err(self.named("slot-order"));
        }
        Ok(self.vp[j as usize])
    }

    /// `publicPart(a)`: the form with each hidden value replaced by what was shown, without `a.e`.
    pub fn public_part(&self, a: &Aff) -> Result<E> {
        let mut v = a.c;
        for x in &a.s {
            v = v + x.1 * self.shown(x.0)?;
        }
        Ok(v)
    }

    /// `claimsIn(tr, slot, n)`: reads `n` hidden values, each sent as `value + mask entry`.
    pub fn claims_in(&mut self, tr: &mut Tr<'_, '_, '_, '_>, slot: &mut u32, n: u32) -> Result<u32> {
        let first = *slot;
        let v = tr_read(tr, n as usize)?;
        for i in 0..n {
            self.hide(*slot + i, v[i as usize], E::one())?;
        }
        *slot = slot.wrapping_add(n);
        Ok(first)
    }

    /// `push(w, a)`: adds `w * a` to the one equation.
    pub fn push(&mut self, w: E, a: &Aff) -> Result<()> {
        if self.door_shut {
            return Err(self.named("f-door"));
        }
        for x in &a.e {
            if x.tree as usize >= self.trees.len()
                || x.row as usize >= self.trees[x.tree as usize].rows.len()
            {
                return Err(self.named("L-row"));
            }
            let row = &mut self.trees[x.tree as usize].rows[x.row as usize];
            let l = &mut row.l;
            if x.idx < row.l0 || x.idx - row.l0 >= l.len() as u64 {
                return Err(self.named("L-index"));
            }
            let at = (x.idx - row.l0) as usize;
            l[at] = l[at] + w * x.coef;
        }
        for x in &a.s {
            if x.0 >= self.ns {
                return Err(self.named("L-slot"));
            }
            self.ls[x.0 as usize] = self.ls[x.0 as usize] + w * x.1;
        }
        self.c0 = self.c0 + w * a.c;
        Ok(())
    }

    /// `batchBy(drawn)`: stores the batching challenge theta.
    pub fn batch_by(&mut self, drawn: E) -> Result<()> {
        if self.theta_drawn {
            return Err(self.named("f-draws"));
        }
        self.theta = drawn;
        self.theta_drawn = true;
        Ok(())
    }

    /// `kapAt(c)`: `theta^c`.
    pub fn kap_at(&self, c: u32) -> Result<E> {
        if !self.theta_drawn {
            return Err(self.named("f-draws"));
        }
        let mut power = E::one();
        let mut square = self.theta;
        let mut e = c;
        while e != 0 {
            if e & 1 != 0 {
                power = power * square;
            }
            e >>= 1;
            square = square * square;
        }
        Ok(power)
    }

    /// `kapTake(c)`.
    pub fn kap_take(&mut self, c: u32) -> Result<E> {
        if self.door_shut {
            return Err(self.named("f-door"));
        }
        if !self.kap_map.is_empty() {
            if c >= self.plan_claims
                || self.kap_map.len() != self.plan_claims as usize
                || self.kap_map[c as usize]
            {
                return Err(self.named("f-draws"));
            }
            self.kap_map[c as usize] = true;
        }
        self.kap_at(c)
    }

    /// `kapAllTakenF()`.
    pub fn kap_all_taken(&self) -> Result<()> {
        if self.kap_map.len() != self.plan_claims as usize {
            return Err(self.named("f-draws"));
        }
        for &x in &self.kap_map {
            if !x {
                return Err(self.named("f-draws"));
            }
        }
        Ok(())
    }

    /// `owe(what)`.
    pub fn owe(&mut self, what: &str) -> Rc<Owed> {
        let o = Rc::new(Owed { what: String::from(what), added: Cell::new(false) });
        self.owed.push(o.clone());
        o
    }

    /// `kap()`.
    pub fn kap(&mut self) -> Result<E> {
        let c = self.n_claim;
        self.n_claim += 1;
        self.kap_take(c)
    }

    /// `lin(f)`: adds the claim that the form is 0.
    pub fn lin(&mut self, f: &Aff) -> Result<()> {
        let kappa = self.kap()?;
        self.push(kappa, f)
    }

    /// `settle(maskCoef, constant, used)`.
    pub fn settle(&self, used: u32) -> Result<(Vec<E>, E)> {
        if used > self.ns || self.got.len() != self.ns as usize {
            return Err(self.named("slot-marks"));
        }
        for o in &self.owed {
            if !o.added.get() {
                return Err(self.named(&format!("claim-not-added-{}", o.what)));
            }
        }
        for j in 0..used {
            if !self.got[j as usize] {
                return Err(self.named("slot-unused"));
            }
        }
        let mut mask_coef = vec![E::zero(); self.ns as usize];
        let mut constant = self.c0;
        for j in 0..self.ns as usize {
            if self.ls[j].is_zero() {
                continue;
            }
            if !self.got[j] {
                return Err(self.named("slot-order"));
            }
            mask_coef[j] = E::zero() - self.ls[j] * self.mf[j];
            constant = constant + self.ls[j] * self.vp[j];
        }
        Ok((mask_coef, constant))
    }
}

/// `trimL(F)` / `fillL(F)`: a plan keeps its trees without the `L` vectors.
pub fn trim_l(f: &mut HFork) {
    for x in &mut f.trees {
        for r in &mut x.rows {
            r.l = Vec::new();
        }
    }
}

/// `fillL(F)`: allocates every virtual row's `L`, all zero.
pub fn fill_l(f: &mut HFork) {
    for x in &mut f.trees {
        for r in &mut x.rows {
            r.l = vec![E::zero(); x.k as usize];
        }
    }
}

/// A product layer: `sum_x eq(rho, x) vL(x) vR(x) = C` (`struct ProductLevel`).
pub struct ProductLevel {
    pub r: Vec<E>,
    pub s_l: u32,
    pub s_r: u32,
    pub tau: E,
    pub row: Aff,
}

/// `readProductLevelRounds`: the mu rounds of one product layer, then `vL`, `vR` and `tau`.
pub fn read_product_level_rounds(
    f: &mut HFork,
    tr: &mut Tr<'_, '_, '_, '_>,
    slot: &mut u32,
    mu: usize,
    rho: &[E],
    c: &Aff,
    order: &[u32],
    calls: &mut crate::hash::calls::HashCalls,
) -> Result<ProductLevel> {
    let mut o = ProductLevel { r: vec![E::zero(); mu], s_l: 0, s_r: 0, tau: E::zero(), row: Aff::default() };
    let mut p = psc_begin(f, tr, slot, c, calls)?;
    for j in 0..mu {
        let v = order[j] as usize;
        o.r[mu - 1 - v] = super::sumcheck::round_in(
            f,
            tr,
            slot,
            super::sumcheck::RoundForm::Eq2,
            &mut p,
            rho[mu - 1 - v],
            0,
            calls,
        )?;
    }
    o.s_l = psc_ends(f, tr, slot, &mut p, 2, 2, calls)?;
    o.s_r = o.s_l + 1;
    o.tau = tr_answer(tr, RoundName::Line, calls)?;
    o.row = psc_row(f, &mut p, f.shown(o.s_l)? * f.shown(o.s_r)?, &Aff::default())?;
    Ok(o)
}

/// `handDown(o, rho, C)`: the next layer's point and start form.
pub fn hand_down(o: &ProductLevel, rho: &mut Vec<E>, c: &mut Aff) {
    rho.clear();
    rho.push(o.tau);
    rho.extend_from_slice(&o.r);
    *c = Aff::slot(o.s_l) * (E::one() - o.tau) + Aff::slot(o.s_r) * o.tau;
}

/// `layerObject(F, o)`: adds the layer's claim.
pub fn layer_object(f: &mut HFork, o: &ProductLevel) -> Result<()> {
    f.lin(&o.row)
}
