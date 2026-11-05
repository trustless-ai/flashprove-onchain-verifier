//! The verifier's approximate range check, ported from `verifier/src/vf_smallness_test.h` and
//! `verifier/src/vf_smallness_test_members.inc`.
//!
//! It is meant to show, for every cell of its matrices, `|cell| < 2^(LBZ + 1) = 2^18`. `Z` is one
//! row's sum of `coefficient * cell`, each column's coefficient a random -1, 0 or 1, in one of
//! `tau` combinations. A tie is a linear claim per matrix; a read, one claim per functional and
//! matrix row segment, equates `sum_i phi[i] Z` with the committed sum in `U3`.
//!
//! The C++ header includes itself into `struct HTailF2`; this port keeps the same state in one
//! struct. The two transcript-independent parts are tested against C++ dumps
//! (`fixtures/subproof_vectors.txt`); the transcript-driven calls are exercised on the Rust chain
//! in `fp-host/tests/subproof_tests.rs`.
//!
//! C++ `refuse()` becomes a [`Refusal`] value. Claim section names (`F.section`) are for the C++
//! test harness only; no verifier decision reads them, so this port leaves them out.

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::{E, F};
use crate::hash::calls::HashCalls;
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::Plan;
use crate::refusal::{Refusal, Result};

use super::common::{eq_one, eq_tab, mix64};
use super::engine::{Aff, HFork, TreeKind};
use super::lookup::{
    forest_elems, forest_join_added, forest_lins, forest_pad, forest_padding_laid,
    forest_planes_added, forest_pub_ask, forest_shape, place_z, u_ent, HCallZ, HForest, HPiece,
};
use super::matrices::TMat;
use super::packing::{tie_left, tie_right, PlaceF, ShP, KCAP, LANES, LRAD};
use super::segment::{t2_add_n, t2_add_p, t2_lin, EqRun, Run2, Tail2};
use super::sumcheck::psc_row;
use super::transcript::{tr_trits, Tr};

/// `T2D0`: the bits of the low digit of `Z + 2^LBZ`.
pub const T2D0: i32 = 10;
/// `T2D1`: the bits of the high digit.
pub const T2D1: i32 = crate::verifier::common::LBZ + 1 - T2D0;

/// `T2Foreign`: a reader's description of a foreign matrix.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct T2Foreign {
    pub name: String,
    pub k: u64,
    pub a: u32,
    pub m: u64,
    pub wp: u32,
}

/// `T2Map`: the indices of the check's trees in `HFork::trees`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct T2Map {
    pub u: [i32; 4],
    pub tt: i32,
    pub bt: i32,
    pub zz: i32,
    pub yy: i32,
    pub kk: i32,
    pub bz: i32,
    pub tx: Vec<i32>,
    pub ft: Vec<i32>,
    pub pk: Vec<i32>,
    pub count: i32,
}

impl Default for T2Map {
    fn default() -> Self {
        Self {
            u: [-1; 4],
            tt: -1,
            bt: -1,
            zz: -1,
            yy: -1,
            kk: -1,
            bz: -1,
            tx: Vec::new(),
            ft: Vec::new(),
            pk: Vec::new(),
            count: 0,
        }
    }
}

/// A segment's check on a sub-proof's arrays (`currentSegment` in C++). S3 supplies the real
/// implementation; `OpenGate` is the test seam.
pub trait SegmentGate {
    /// `fixedBeforeTheMatrixF`.
    fn fixed_before_the_matrix(
        &mut self,
        f: &HFork,
        gt_tree: &[u32],
        u_trees: &[i32; 4],
    ) -> Result<()>;
    /// `rootInH`: receives the next commit point's roots.
    fn root_in_h(
        &mut self,
        f: &mut HFork,
        tr: &mut Tr<'_, '_, '_, '_>,
        trees: &[i32],
        calls: &mut crate::hash::calls::HashCalls,
    ) -> Result<()>;
}

/// A gate for tests and for planning runs: it accepts and marks the named trees committed. It is
/// not the frame check that S3 will install.
#[derive(Default)]
pub struct OpenGate;

impl SegmentGate for OpenGate {
    fn fixed_before_the_matrix(
        &mut self,
        _f: &HFork,
        _gt_tree: &[u32],
        _u_trees: &[i32; 4],
    ) -> Result<()> {
        Ok(())
    }

    fn root_in_h(
        &mut self,
        f: &mut HFork,
        _tr: &mut Tr<'_, '_, '_, '_>,
        trees: &[i32],
        _calls: &mut crate::hash::calls::HashCalls,
    ) -> Result<()> {
        for &t in trees {
            if t < 0 || t as usize >= f.trees.len() || f.trees[t as usize].root {
                return Err(Refusal::internal(&format!("{}plan-link", f.g)));
            }
            f.trees[t as usize].root = true;
        }
        Ok(())
    }
}

/// `eB(v)`: `v` as a base-field element.
#[inline]
fn eb(v: u64) -> E {
    E::from_base(F::from_u64(v))
}

/// `eS(x, s)`.
#[inline]
fn es(x: E, s: u64) -> E {
    super::packing::e_scale(x, s)
}

/// `t2BL(R)`: splits rows `0 .. R - 1` into blocks (first row, length), each length the largest
/// power of two that still fits.
pub fn t2_bl(r: u64) -> Result<Vec<(u64, u64)>> {
    let mut o = Vec::new();
    let mut r0 = 0u64;
    while r0 < r {
        let mut rp = 1u64;
        while 2 * rp <= r - r0 {
            rp *= 2;
        }
        if r0 & (rp - 1) != 0 {
            return Err(Refusal::internal("internal-t2f-blocks"));
        }
        o.push((r0, rp));
        r0 += rp;
    }
    Ok(o)
}

/// `t2fKappaByText`: `theta^c`, one factor at a time (self-tests only).
pub fn t2f_kappa_by_text(theta: E, c: u32) -> E {
    let mut power = E::one();
    for _ in 0..c {
        power = power * theta;
    }
    power
}

/// One sub-proof's range check (`struct HTailF2`).
#[derive(Clone, Debug)]
pub struct HTailF2 {
    pub mz: u64,
    pub nm: usize,
    pub mats: Vec<TMat>,
    pub off: Vec<u64>,
    pub col0: Vec<u64>,
    pub gt_tree: Vec<u32>,
    pub gt_row: Vec<u32>,
    pub k_tx: Vec<u64>,
    pub ft: Vec<T2Foreign>,
    pub ix: T2Map,
    pub z: [HCallZ; 4],
    pub f9: HForest,
    pub f9_ran: bool,
    pub cf: Vec<i8>,
    pub cf_first: Vec<u64>,
    pub vt: Vec<E>,
    pub vp: Vec<E>,
    pub join_obj9: u32,
    pub tau: u32,
    pub lidb: i32,
    // The members of `vf_smallness_test_members.inc`.
    pub pk_mat: Vec<usize>,
    pub px_mat: Vec<usize>,
    pub shp: Vec<ShP>,
    pub n_xof: Vec<u32>,
    pub row_x: Vec<Vec<E>>,
    pub lo_x: Vec<Vec<E>>,
    pub eq_first: Vec<u64>,
    pub gam_x: Vec<Vec<E>>,
    pub gam_v: Vec<Vec<E>>,
    pub tie_obj: Vec<u32>,
    pub ties_on: Vec<u32>,
    pub fun_laid: Vec<super::lookup::HFun>,
    pub n_u: [u64; 3],
    pub tab_first: [u64; 2],
    pub tab_len: [u64; 2],
    pub n_x4_laid: usize,
    pub fun_at_close: usize,
    pub fun_closed: bool,
    pub fun_hash: [u32; 8],
    pub fold_drawn: u32,
    pub slot_a: u32,
    pub slot_b: u32,
    pub ls_tail: Vec<E>,
    pub pl_own: Vec<PlaceF>,
    pub pl_for: Vec<PlaceF>,
    pub shape_rec: Vec<ShP>,
    pub fold_taken: Vec<bool>,
    pub bit_factor9: E,
}

impl Default for HTailF2 {
    fn default() -> Self {
        Self::new()
    }
}

impl HTailF2 {
    pub fn new() -> Self {
        Self {
            mz: 0,
            nm: 0,
            mats: Vec::new(),
            off: Vec::new(),
            col0: Vec::new(),
            gt_tree: Vec::new(),
            gt_row: Vec::new(),
            k_tx: Vec::new(),
            ft: Vec::new(),
            ix: T2Map::default(),
            z: core::array::from_fn(|_| HCallZ::default()),
            f9: HForest::new(),
            f9_ran: false,
            cf: Vec::new(),
            cf_first: Vec::new(),
            vt: Vec::new(),
            vp: Vec::new(),
            join_obj9: u32::MAX,
            tau: 0,
            lidb: 0,
            pk_mat: Vec::new(),
            px_mat: Vec::new(),
            shp: Vec::new(),
            n_xof: Vec::new(),
            row_x: Vec::new(),
            lo_x: Vec::new(),
            eq_first: Vec::new(),
            gam_x: Vec::new(),
            gam_v: Vec::new(),
            tie_obj: Vec::new(),
            ties_on: Vec::new(),
            fun_laid: Vec::new(),
            n_u: [0; 3],
            tab_first: [0; 2],
            tab_len: [0; 2],
            n_x4_laid: 0,
            fun_at_close: 0,
            fun_closed: false,
            fun_hash: [0; 8],
            fold_drawn: 0,
            slot_a: 0,
            slot_b: 0,
            ls_tail: Vec::new(),
            pl_own: Vec::new(),
            pl_for: Vec::new(),
            shape_rec: Vec::new(),
            fold_taken: Vec::new(),
            bit_factor9: E::zero(),
        }
    }

    /// `zzBlocks()`.
    fn zz_blocks(&self) -> usize {
        t2_bl(self.tau as u64).map(|v| v.len()).unwrap_or(0)
    }

    /// `zzRowReads()`.
    fn zz_row_reads(&self) -> u32 {
        2 * self.zz_blocks() as u32
    }

    /// `zzRowTies()`.
    fn zz_row_ties(&self) -> u32 {
        2 * self.zz_blocks() as u32 + 1
    }

    /// `zzCol(mu, plane, i)`.
    fn zz_col(&self, mu: usize, plane: i32, i: u64) -> Result<u64> {
        if mu >= self.nm || !(0..=1).contains(&plane) || i >= self.mats[mu].m {
            return Err(Refusal::internal("internal-f-zzcol"));
        }
        Ok(plane as u64 * self.mz + self.off[mu] + i)
    }

    /// `tabAt(Fn, c, sg)`.
    fn tab_at(&self, fun: &super::lookup::HFun, c: u64, sg: u64) -> Result<u64> {
        if fun.m < 0 || fun.m as usize >= self.nm || fun.l == 0 {
            return Err(Refusal::internal(&format!("internal-t2f-functional-{}", fun.name)));
        }
        let m = &self.mats[fun.m as usize];
        let nsg = m.m / fun.l;
        if c >= m.k || sg >= nsg {
            return Err(Refusal::internal("internal-f-table-index"));
        }
        Ok(fun.at + c * nsg + sg)
    }

    /// `piecesF`: builds the lookup calls `z[1]` (R10z) and `z[2]` (R8d), their pieces, and `f9`.
    fn pieces_f(&mut self) -> Result<()> {
        for x in &mut self.z {
            *x = HCallZ::default();
        }
        let blocks = t2_bl(self.tau as u64)?;
        if blocks.is_empty() || blocks.len() > 2 {
            return Err(Refusal::internal("internal-t2f-blocks"));
        }
        for (i, b) in blocks.iter().enumerate() {
            self.z[1].pc.push(HPiece {
                tree: self.ix.zz,
                row: i as i32,
                r0: b.0,
                rp: b.1,
                c0: 0,
                cp: self.mz,
                ..HPiece::default()
            });
        }
        for (i, b) in blocks.iter().enumerate() {
            self.z[2].pc.push(HPiece {
                tree: self.ix.zz,
                row: (blocks.len() + i) as i32,
                r0: b.0,
                rp: b.1,
                c0: self.mz,
                cp: self.mz,
                ..HPiece::default()
            });
        }
        place_z(&mut self.z[1], "R10z", T2D0, self.lidb)?;
        place_z(&mut self.z[2], "R8d", T2D1, self.lidb)?;
        for q in 1..=2 {
            if self.z[q].c.n < 10 {
                return Err(Refusal::named("hid-call-floor"));
            }
        }
        let calls = [self.z[1].c.clone(), self.z[2].c.clone()];
        self.f9 = forest_shape(&calls, self.lidb)?;
        self.f9_ran = false;
        self.f9.pub_ = vec![0; self.f9.nt as usize];
        for q in 0..2 {
            let mut end = 0u64;
            let pc: Vec<HPiece> = self.z[1 + q].pc.clone();
            for p in &pc {
                if p.cp < p.c_p {
                    for rr in 0..p.rp {
                        self.f9.pub_run(
                            q as i32,
                            p.off + rr * p.c_p + p.cp,
                            p.c_p - p.cp,
                        )?;
                    }
                }
                end = end.max(p.off + (1u64 << p.b));
            }
            let n = 1u64 << self.z[1 + q].c.n;
            self.f9.pub_run(q as i32, end, n - end)?;
        }
        let names = self.f9.names.clone();
        let pub_ = self.f9.pub_.clone();
        forest_pub_ask(&self.f9, &names, &pub_, "")?;
        Ok(())
    }

    /// `shapeF`: sets the check's sizes and tree list from the fold list.
    pub fn shape(
        &mut self,
        m: &[TMat],
        tx_of: &[i32],
        f: &[T2Foreign],
        has_u: [bool; 4],
        tau: u32,
        lidb: i32,
    ) -> Result<()> {
        self.mats = m.to_vec();
        self.ft = f.to_vec();
        self.nm = self.mats.len();
        self.mz = 0;
        self.off.clear();
        self.col0.clear();
        self.gt_tree.clear();
        self.gt_row.clear();
        self.k_tx.clear();
        self.pk_mat.clear();
        self.px_mat.clear();
        self.shp.clear();
        self.n_xof.clear();
        self.tau = tau;
        self.lidb = lidb;
        if tx_of.len() != self.nm || has_u[3] {
            return Err(Refusal::internal("internal-t2f-lists"));
        }
        for (mu, mat) in self.mats.iter().enumerate() {
            if mat.kind == 0 {
                if tx_of[mu] >= 0 {
                    if tx_of[mu] as usize != self.px_mat.len() {
                        return Err(Refusal::internal("internal-t2f-TX-order"));
                    }
                    self.px_mat.push(mu);
                    self.k_tx.push(mat.k);
                } else {
                    self.pk_mat.push(mu);
                }
            }
        }
        if self.nm >= 256 {
            return Err(Refusal::named("plan-link"));
        }
        // The list of trees: U1 .. U3 (those that the sub-proof has), PK_i, PX_i, ZZ, BZ, PF_i.
        self.ix = T2Map::default();
        for n in 0..4 {
            if has_u[n] {
                self.ix.u[n] = self.ix.count;
                self.ix.count += 1;
            }
        }
        for _ in 0..self.pk_mat.len() {
            self.ix.pk.push(self.ix.count);
            self.ix.count += 1;
        }
        for _ in 0..self.px_mat.len() {
            self.ix.tx.push(self.ix.count);
            self.ix.count += 1;
        }
        self.ix.zz = self.ix.count;
        self.ix.count += 1;
        self.ix.bz = self.ix.count;
        self.ix.count += 1;
        for _ in 0..self.ft.len() {
            self.ix.ft.push(self.ix.count);
            self.ix.count += 1;
        }
        let mut next_f = 0usize;
        let mut n_pk = 0usize;
        self.pl_own = vec![PlaceF::default(); self.px_mat.len()];
        self.pl_for = vec![PlaceF::default(); self.ft.len()];
        for mu in 0..self.nm {
            let mat = self.mats[mu].clone();
            if mat.m == 0 {
                return Err(Refusal::named(&format!("shape-matrix-{}", mat.name)));
            }
            if mat.k == 0 || mat.k > KCAP {
                return Err(Refusal::named("hid-k-range"));
            }
            self.off.push(self.mz);
            self.mz += mat.m;
            self.col0.push(0);
            self.gt_row.push(0);
            if mat.kind == 0 && tx_of[mu] < 0 {
                self.gt_tree.push(self.ix.pk[n_pk] as u32);
                self.n_xof.push(48 + n_pk as u32);
                n_pk += 1;
            } else if mat.kind == 0 {
                let tx = tx_of[mu] as usize;
                self.gt_tree.push(self.ix.tx[tx] as u32);
                self.n_xof.push(32 + tx as u32);
                let pl = &mut self.pl_own[tx];
                pl.col0 = *self.col0.last().unwrap();
                pl.k = mat.k;
                pl.m = mat.m;
                pl.have_matrix = true;
            } else if mat.kind == 1 {
                let fi = mat.foreign;
                if fi < 0
                    || fi as usize >= self.ft.len()
                    || mat.tt_off != 0
                    || mat.k != self.ft[fi as usize].k
                    || mat.m != self.ft[fi as usize].m
                    || mat.wp != self.ft[fi as usize].wp
                {
                    return Err(Refusal::named(&format!("shape-foreign-{}", mat.name)));
                }
                if fi as usize != next_f {
                    return Err(Refusal::internal("internal-t2f-ZF-order"));
                }
                next_f += 1;
                self.gt_tree.push(self.ix.ft[fi as usize] as u32);
                self.n_xof.push(10 + fi as u32);
                let pl = &mut self.pl_for[fi as usize];
                pl.col0 = mat.tt_off;
                pl.k = mat.k;
                pl.m = mat.m;
                pl.have_matrix = true;
            } else {
                return Err(Refusal::named("t2f-weight-class"));
            }
        }
        if next_f != self.ft.len() {
            return Err(Refusal::internal("internal-t2f-ZF-order"));
        }
        for mu in 0..self.nm {
            self.n_xof[mu] = mu as u32;
        }
        if 2 * self.mz >= (1u64 << 32) {
            return Err(Refusal::named("t2f-columns-range"));
        }
        self.pieces_f()
    }

    /// `lins(nX4)`: the number of linear claims that `objectsF()` adds.
    pub fn lins(&self, n_x4: usize) -> usize {
        forest_lins(&self.f9) + 4 + self.nm + n_x4
    }

    /// `bzColumns()`.
    pub fn bz_columns(&self) -> u64 {
        1u64 << (self.f9.k_t + self.f9.c_k)
    }

    /// `smallElems()`: the check's number of message slots.
    pub fn small_elems(&self) -> usize {
        forest_elems(&self.f9)
    }

    /// `groupsRun()`: 1 once the check's lookup has run.
    pub fn groups_run(&self) -> usize {
        if self.f9_ran {
            1
        } else {
            0
        }
    }

    /// `addTreesF`: adds U1 .. U3, the PK_i, the PX_i, ZZ, BZ and the PF_i, in this order.
    pub fn add_trees(
        &mut self,
        f: &mut HFork,
        t: &mut Tail2,
        n_u: [u64; 3],
        a_tx: &[u32],
        hb: u32,
        stated_hb: u32,
    ) -> Result<()> {
        if !t.nt.is_empty() {
            return Err(Refusal::internal(&format!("{}internal-t2-order", f.g)));
        }
        t.link = true;
        if a_tx.len() != self.px_mat.len() {
            return Err(Refusal::internal("internal-t2f-lists"));
        }
        if self.tau < stated_hb {
            return Err(Refusal::named("policy-tau-hb"));
        }
        let must = |got: u32, want: i32, f: &HFork| -> Result<()> {
            if got as i32 != want {
                return Err(Refusal::internal(&format!("{}internal-t2f-map", f.g)));
            }
            Ok(())
        };
        // C++ `addTreesF` keeps the lengths in `nUF`; `objectsF`, `selfTestF` and `tileSelfTestF`
        // read them.
        self.n_u = n_u;
        let n_u = n_u;
        self.tab_first[0] = 0;
        self.tab_len[0] = 0;
        self.tab_first[1] = 0;
        self.tab_len[1] = if self.ix.u[2] >= 0 { n_u[2] } else { 0 };
        if self.ix.u[3] >= 0 {
            return Err(Refusal::internal(&format!("{}internal-t2f-lists", f.g)));
        }
        let un = ["U1", "U2", "U3"];
        for n in 0..3 {
            if self.ix.u[n] >= 0 {
                let got = t2_add_n(f, t, un[n], 1, n_u[n], super::common::CE as u32, 1, false, 1)?;
                must(got, self.ix.u[n], f)?;
            }
        }
        for i in 0..self.pk_mat.len() {
            let mat = self.mats[self.pk_mat[i]].clone();
            let got = t2_add_p(f, t, &format!("PK{}", i), mat.m, mat.k, mat.wp, 1, false)?;
            must(got, self.ix.pk[i], f)?;
        }
        for i in 0..self.px_mat.len() {
            let mat = self.mats[self.px_mat[i]].clone();
            let got = t2_add_p(f, t, &format!("PX{}", i), mat.m, mat.k, mat.wp, a_tx[i], false)?;
            must(got, self.ix.tx[i], f)?;
        }
        let got = t2_add_n(
            f,
            t,
            "ZZ",
            self.tau as u64,
            2 * self.mz,
            1,
            1,
            false,
            2 * self.zz_blocks() as u32 + 2,
        )?;
        must(got, self.ix.zz, f)?;
        let got = t2_add_n(f, t, "BZ", 32, self.bz_columns(), 1, 1, false, 3)?;
        must(got, self.ix.bz, f)?;
        for i in 0..self.ft.len() {
            let ft = self.ft[i].clone();
            let got = t2_add_p(f, t, &ft.name, ft.m, ft.k, ft.wp, ft.a, true)?;
            must(got, self.ix.ft[i], f)?;
        }
        let declared = |pl: &mut PlaceF, t: &Tail2, ti: usize, hb: u32| {
            let n = &t.nt[ti];
            pl.sh = n.shape.clone();
            pl.have_shape = true;
            pl.hb = hb;
            pl.m_s = n.shape.m_s;
            pl.lanes = LANES as u64;
            pl.pad_rows = n.shape.r * n.shape.j;
            pl.j = n.shape.j;
            pl.kk = n.shape.k;
            pl.off = 0;
            pl.w = n.shape.w as u32;
        };
        for i in 0..self.px_mat.len() {
            declared(&mut self.pl_own[i], t, self.ix.tx[i] as usize, hb);
            self.pl_own[i].root_index = (self.pk_mat.len() + i) as i32;
        }
        for i in 0..self.ft.len() {
            declared(&mut self.pl_for[i], t, self.ix.ft[i] as usize, hb);
        }
        self.shp = vec![ShP::default(); self.nm];
        for mu in 0..self.nm {
            self.shp[mu] = t.nt[self.gt_tree[mu] as usize].shape.clone();
            if self.shp[mu].m != self.mats[mu].m || self.shp[mu].k != self.mats[mu].k {
                return Err(Refusal::internal(&format!("{}internal-t2f-map", f.g)));
            }
        }
        self.shape_rec = self.shp.clone();
        Ok(())
    }

    /// `closeFuns`: closes the list of functionals before Cf is drawn.
    pub fn close_funs(&mut self, fun: &[super::lookup::HFun]) -> Result<()> {
        if self.fun_closed {
            return Err(Refusal::internal("internal-f-fun-closed"));
        }
        self.fun_closed = true;
        self.fun_at_close = fun.len();
        fun_digest(fun, &mut self.fun_hash);
        Ok(())
    }

    /// `funsHeld`: the list must not change after it is closed.
    pub fn funs_held(&self, f: &HFork, fun: &[super::lookup::HFun]) -> Result<()> {
        let mut h = [0u32; 8];
        fun_digest(fun, &mut h);
        if !self.fun_closed || fun.len() != self.fun_at_close || h != self.fun_hash {
            return Err(Refusal::internal(&format!("{}internal-f-fun-moved", f.g)));
        }
        Ok(())
    }

    /// `funOpen`.
    pub fn fun_open(&self) -> Result<()> {
        if self.fun_closed {
            return Err(Refusal::internal("internal-f-fun-closed"));
        }
        Ok(())
    }

    /// `drawMatrixF`: draws Cf, the coefficients in {-1, 0, 1} of the combinations.
    pub fn draw_matrix(&mut self, tr: &mut Tr<'_, '_, '_, '_>, calls: &mut HashCalls) -> Result<()> {
        self.cf_first = vec![0; self.nm + 1];
        for mu in 0..self.nm {
            self.cf_first[mu + 1] = self.cf_first[mu] + self.mats[mu].k;
        }
        self.cf = tr_trits(
            tr,
            self.cf_first[self.nm] as usize,
            self.tau as usize,
            calls,
        )?;
        Ok(())
    }

    /// `planRounds`: plans the check's rounds on the hash chain.
    pub fn plan_rounds(&self, p: &mut Plan, where_: &str, which: u32) -> Result<()> {
        if which == 0 {
            let columns: u64 = self.mats.iter().map(|m| m.k).sum();
            if crate::numbers::blocks::rng_combinations_plan(p) != self.tau {
                return Err(Refusal::named("plan-tau"));
            }
            crate::numbers::blocks::plan_rng(p, where_, columns);
            return Ok(());
        }
        if which != 1 {
            return Err(Refusal::internal("internal-plan-moment"));
        }
        super::lookup::forest_plan(p, &format!("{}, digits", where_), &self.f9);
        Ok(())
    }

    /// `stepF()`.
    fn step_f(&self) -> u64 {
        1u64 << ceil_log2(self.tau as u64)
    }

    /// `equationsF(nX4)`.
    pub fn equations(&self, n_x4: usize) -> u64 {
        let mut n = 0u64;
        for m in &self.mats {
            n += self.step_f() << ceil_log2((m.m + 2) / 3);
        }
        n + n_x4 as u64 * self.step_f()
    }

    /// `equationsLaidF()`.
    pub fn equations_laid(&self) -> Result<u64> {
        if self.eq_first.len() != self.nm + 1 {
            return Err(Refusal::internal("internal-f-draws"));
        }
        Ok(self.eq_first[self.nm] + self.n_x4_laid as u64 * self.step_f())
    }

    /// `powersF`: once theta is drawn, sets `vt`, `vp`, `rowX`, `loX`, `eqFirst`.
    pub fn powers(&mut self, f: &HFork) -> Result<()> {
        if !f.theta_drawn || f.plan_claims == 0 {
            return Err(Refusal::internal(&format!("{}internal-f-draws", f.g)));
        }
        self.vt = vec![E::one(); self.tau as usize];
        for u in 1..self.tau as usize {
            self.vt[u] = self.vt[u - 1] * f.theta;
        }
        self.vp = self.vt.clone();
        let step = f.theta.pow(self.step_f());
        self.eq_first = vec![0; self.nm + 1];
        self.row_x = vec![Vec::new(); self.nm];
        self.lo_x = vec![Vec::new(); self.nm];
        for mu in 0..self.nm {
            let s = self.shp[mu].clone();
            if s.j != 1
                || s.rd != 0
                || s.r != s.m_s
                || s.rr != s.m_s
                || s.m_s != (self.mats[mu].m + 2) / 3
            {
                return Err(Refusal::internal(&format!("{}internal-sym-shape", f.g)));
            }
            self.eq_first[mu + 1] = self.eq_first[mu] + (self.step_f() << ceil_log2(s.m_s));
            self.row_x[mu] = vec![E::one(); s.m_s as usize];
            for i in 1..s.m_s as usize {
                self.row_x[mu][i] = self.row_x[mu][i - 1] * step;
            }
            self.lo_x[mu] = vec![E::one()];
        }
        Ok(())
    }

    /// `leadF(first)`: the factor that raises the next claim's `theta^nClaim`.
    fn lead(&self, f: &HFork, first: u64) -> Result<E> {
        if f.n_claim >= f.plan_claims {
            return Err(Refusal::internal(&format!("{}internal-f-draws", f.g)));
        }
        Ok(f.theta.pow((f.plan_claims - f.n_claim) as u64 + first))
    }

    /// `transcriptF`: Cf, the commitment to ZZ and BZ, the lookup on the digits.
    pub fn transcript<G: SegmentGate + ?Sized>(
        &mut self,
        f: &mut HFork,
        tr: &mut Tr<'_, '_, '_, '_>,
        slot: &mut u32,
        tail: &Tail2,
        gate: &mut G,
        calls: &mut HashCalls,
    ) -> Result<()> {
        if !self.fun_closed {
            return Err(Refusal::internal(&format!("{}internal-f-fun-open", f.g)));
        }
        if self.shp.len() != self.nm {
            return Err(Refusal::internal(&format!("{}internal-t2f-map", f.g)));
        }
        self.slot_a = *slot;
        gate.fixed_before_the_matrix(f, &self.gt_tree, &self.ix.u)?;
        self.draw_matrix(tr, calls)?;
        self.fold_drawn += 1;
        gate.root_in_h(f, tr, &[self.ix.zz, self.ix.bz], calls)?;
        if !f.trees[self.ix.zz as usize].root || !f.trees[self.ix.bz as usize].root {
            return Err(Refusal::internal(&format!("{}internal-f-order", f.g)));
        }
        // The lookup on the digits.
        let pub9 = self.f9.pub_.clone();
        let calls9 = [self.z[1].c.clone(), self.z[2].c.clone()];
        self.f9 = forest_pad(f, tr, &calls9, &pub9, slot, self.lidb, calls)?;
        self.f9_ran = true;
        for q in 0..2 {
            self.z[1 + q].c.alpha = self.f9.alpha;
            self.z[1 + q].c.zk = self.f9.zk[q].clone();
        }
        if !tail.link {
            return Err(Refusal::internal(&format!("{}internal-root-behind-sd", f.g)));
        }
        self.slot_b = *slot;
        Ok(())
    }

    /// `coefficientsF`: sets the row weights of the virtual rows.
    pub fn coefficients(&self, f: &mut HFork) -> Result<()> {
        fn point(row: &mut super::engine::HRow, z: &[E], n: usize, first: u64) {
            row.row_form = true;
            row.row_ones = false;
            row.row_point = z[..n].to_vec();
            row.row_first = first;
        }
        fn powers(row: &mut super::engine::HRow, mut base: E, rows: u64) {
            row.row_form = true;
            row.row_ones = false;
            row.row_point.clear();
            row.row_first = 0;
            let bits = ceil_log2(rows) as usize;
            row.row_lo = vec![E::one(); bits];
            row.row_hi.clear();
            for _ in 0..bits {
                row.row_hi.push(base);
                base = base * base;
            }
        }
        fn ones(row: &mut super::engine::HRow) {
            row.row_form = true;
            row.row_ones = true;
            row.row_point.clear();
            row.row_first = 0;
        }
        for n in 0..4 {
            if self.ix.u[n] >= 0 && f.trees[self.ix.u[n] as usize].kind == TreeKind::N {
                let row = &mut f.trees[self.ix.u[n] as usize].rows[0];
                row.coef = vec![E::one()];
                ones(row);
            }
        }
        for q in 1..=2 {
            let pc = self.z[q].pc.clone();
            for p in &pc {
                // zrOf(): the last p.b coordinates (the piece's window), not the tail after them.
                let zr = &self.z[q].c.zk[(self.z[q].c.n - p.b) as usize..];
                let e = eq_tab(zr, p.a as usize);
                let mut w = vec![E::zero(); f.trees[p.tree as usize].r as usize];
                for r in 0..p.rp as usize {
                    w[p.r0 as usize + r] = e[r];
                }
                f.trees[p.tree as usize].rows[p.row as usize].coef = w;
                point(
                    &mut f.trees[p.tree as usize].rows[p.row as usize],
                    zr,
                    p.a as usize,
                    p.r0,
                );
            }
        }
        f.trees[self.ix.zz as usize].rows[self.zz_row_reads() as usize].coef = self.vt.clone();
        f.trees[self.ix.zz as usize].rows[self.zz_row_ties() as usize].coef = self.vp.clone();
        for r in [self.zz_row_reads(), self.zz_row_ties()] {
            powers(
                &mut f.trees[self.ix.zz as usize].rows[r as usize],
                f.theta,
                self.tau as u64,
            );
        }
        for e in 0..2 {
            let zb = self.f9.zb[e].clone();
            f.trees[self.ix.bz as usize].rows[e].coef = eq_tab(&zb, 5);
            point(&mut f.trees[self.ix.bz as usize].rows[e], &zb, 5, 0);
        }
        f.trees[self.ix.bz as usize].rows[2].coef = vec![E::one(); 32];
        ones(&mut f.trees[self.ix.bz as usize].rows[2]);
        // A symbol tree's one virtual row is for its tie.
        for mu in 0..self.nm {
            let row = &mut f.trees[self.gt_tree[mu] as usize].rows[0];
            row.coef = self.row_x[mu].clone();
            powers(row, f.theta.pow(self.step_f()), self.shp[mu].m_s);
        }
        Ok(())
    }

    /// `foldAllTakenF`.
    pub fn fold_all_taken(&self, f: &HFork) -> Result<()> {
        if self.fold_taken.len() != self.nm {
            return Err(Refusal::internal(&format!("{}internal-f-draws", f.g)));
        }
        for &x in &self.fold_taken {
            if !x {
                return Err(Refusal::internal(&format!("{}internal-f-draws", f.g)));
            }
        }
        Ok(())
    }

    /// `foldSums(mu, gx, gv)`.
    pub fn fold_sums(&mut self, mu: usize, gx: &mut Vec<E>, gv: &mut Vec<E>) -> Result<()> {
        if self.fold_taken.len() != self.nm {
            self.fold_taken = vec![false; self.nm];
        }
        if mu >= self.nm || self.fold_taken[mu] {
            return Err(Refusal::internal("internal-f-draws"));
        }
        self.fold_taken[mu] = true;
        let k = self.mats[mu].k as usize;
        // Fill directly; the previous `vec![E::zero(); k]` wrote every entry twice.
        let mut xv = Vec::with_capacity(k);
        let mut vv = Vec::with_capacity(k);
        for c in 0..k {
            let base = (self.cf_first[mu] as usize + c) * self.tau as usize;
            let mut px = [0u128; 3];
            let mut nx = [0u128; 3];
            let mut pv = [0u128; 3];
            let mut nv = [0u128; 3];
            for u in 0..self.tau as usize {
                let cf = self.cf[base + u];
                if cf == 0 {
                    continue;
                }
                let neg = cf < 0;
                for i in 0..3 {
                    let a = self.vp[u].0[i].0 as u128;
                    let b = self.vt[u].0[i].0 as u128;
                    if neg {
                        nx[i] += a;
                        nv[i] += b;
                    } else {
                        px[i] += a;
                        pv[i] += b;
                    }
                }
            }
            let mut x = E::zero();
            let mut v = E::zero();
            for i in 0..3 {
                x.0[i] = F(super::common::fred_diff(px[i], nx[i]));
                v.0[i] = F(super::common::fred_diff(pv[i], nv[i]));
            }
            xv.push(x);
            vv.push(v);
        }
        *gx = xv;
        *gv = vv;
        Ok(())
    }

    /// `objectsF`: adds the claims, in this order: the lookup's, the ties, the reads.
    pub fn objects(&mut self, f: &mut HFork, fun: &[super::lookup::HFun]) -> Result<()> {
        if !self.fun_closed || fun.len() != self.fun_at_close {
            return Err(Refusal::internal(&format!("{}internal-f-fun-closed", f.g)));
        }
        self.funs_held(f, fun)?;
        self.fun_laid = fun.to_vec();
        for j in self.slot_a..self.slot_b {
            if !f.ls[j as usize].is_zero() {
                return Err(Refusal::internal(&format!("{}internal-f-tail-slot", f.g)));
            }
        }
        let m1 = E::zero() - E::one();
        let laid = |f: &HFork, before: u32, want: usize| -> Result<()> {
            if (f.n_claim - before) as usize != want {
                return Err(Refusal::internal(&format!("{}internal-f-exist", f.g)));
            }
            Ok(())
        };
        if !self.f9_ran || self.f9.nc != 2 {
            return Err(Refusal::internal(&format!("{}internal-f-exist", f.g)));
        }
        {
            let mut b = f.n_claim;
            super::lookup::forest_objects(f, &self.f9)?;
            laid(f, b, 31 + self.f9.v() as usize + self.f9.d() as usize + 1)?;
            b = f.n_claim;
            self.lin_join9(f)?;
            self.lin_bits9(f)?;
            laid(f, b, 4)?;
        }
        self.powers(f)?;
        self.gam_x = vec![Vec::new(); self.nm];
        self.gam_v = vec![Vec::new(); self.nm];
        for mu in 0..self.nm {
            let mut gx = Vec::new();
            let mut gv = Vec::new();
            self.fold_sums(mu, &mut gx, &mut gv)?;
            self.gam_x[mu] = gx;
            self.gam_v[mu] = gv;
        }
        let mut sx = E::zero();
        for &x in &self.vp {
            sx = sx + x;
        }
        let mut sv = E::zero();
        for &x in &self.vt {
            sv = sv + x;
        }
        // The ties, mu ascending, one linear claim each.
        self.tie_obj = vec![u32::MAX; self.nm];
        self.ties_on = vec![0; f.trees.len()];
        for mu in 0..self.nm {
            let s = self.shp[mu].clone();
            let wl = tie_left(&s, &self.row_x[mu], &self.lo_x[mu])?;
            let wr = tie_right(&s, &self.lo_x[mu], &self.gam_x[mu])?;
            let mut sw = E::zero();
            for &x in &wl {
                sw = sw + x;
            }
            self.tie_obj[mu] = f.n_claim;
            let lead = self.lead(f, self.eq_first[mu])?;
            let aff = Aff::constant(E::zero() - lead * es(sx * sw, 1u64 << crate::verifier::common::LBZ));
            let runs = [
                Run2 {
                    tree: self.ix.zz as u32,
                    row: self.zz_row_ties(),
                    first: self.zz_col(mu, 0, 0)?,
                    coef: lead,
                    w: Some(&wl),
                    w0: 0,
                    n: s.m,
                },
                Run2 {
                    tree: self.ix.zz as u32,
                    row: self.zz_row_ties(),
                    first: self.zz_col(mu, 1, 0)?,
                    coef: es(lead, 1u64 << T2D0),
                    w: Some(&wl),
                    w0: 0,
                    n: s.m,
                },
                Run2 {
                    tree: self.gt_tree[mu],
                    row: 0,
                    first: 0,
                    coef: m1 * lead,
                    w: Some(&wr),
                    w0: 0,
                    n: s.j * s.k,
                },
            ];
            t2_lin(f, &aff, &runs)?;
            self.ties_on[self.gt_tree[mu] as usize] += 1;
        }
        // The reads (X4): one claim per functional and row segment.
        let mut rd_u = [vec![false; self.tab_len[0] as usize], vec![false; self.tab_len[1] as usize]];
        self.n_x4_laid = 0;
        let funs = fun.to_vec();
        for mu in 0..self.nm {
            let mat = self.mats[mu].clone();
            let gc = self.gam_v[mu].clone();
            for un in [0u32, 2u32] {
                for fnn in &funs {
                    if fnn.m != mu as i32 || fnn.tree != un {
                        continue;
                    }
                    if self.ix.u[un as usize] < 0 {
                        return Err(Refusal::internal(&format!("internal-t2f-unit-{}", fnn.name)));
                    }
                    if fnn.l == 0 || mat.m % fnn.l != 0 || fnn.phi.len() as u64 != fnn.l {
                        return Err(Refusal::named(&format!("shape-functional-{}", fnn.name)));
                    }
                    let nsg = mat.m / fnn.l;
                    let t0 = self.tab_first[(un / 2) as usize];
                    let mut sphi = E::zero();
                    for &x in &fnn.phi {
                        sphi = sphi + x;
                    }
                    for sg in 0..nsg {
                        let lead =
                            self.lead(f, self.eq_first[self.nm] + self.n_x4_laid as u64 * self.step_f())?;
                        let mut aff = Aff::constant(
                            E::zero() - lead * es(sphi * sv, 1u64 << crate::verifier::common::LBZ),
                        );
                        for c in 0..mat.k {
                            let at = self.tab_at(fnn, c, sg)?;
                            let rd = &mut rd_u[(un / 2) as usize];
                            if at < t0
                                || at - t0 >= rd.len() as u64
                                || rd[(at - t0) as usize]
                                || gc[c as usize].is_zero()
                            {
                                return Err(Refusal::internal(&format!(
                                    "{}internal-f-table-read",
                                    f.g
                                )));
                            }
                            rd[(at - t0) as usize] = true;
                            aff.add(
                                &u_ent(f, self.ix.u[un as usize] as u32, at)?,
                                E::zero() - lead * gc[c as usize],
                            );
                        }
                        let runs = [
                            Run2 {
                                tree: self.ix.zz as u32,
                                row: self.zz_row_reads(),
                                first: self.zz_col(mu, 0, sg * fnn.l)?,
                                coef: lead,
                                w: Some(&fnn.phi),
                                w0: 0,
                                n: fnn.l,
                            },
                            Run2 {
                                tree: self.ix.zz as u32,
                                row: self.zz_row_reads(),
                                first: self.zz_col(mu, 1, sg * fnn.l)?,
                                coef: es(lead, 1u64 << T2D0),
                                w: Some(&fnn.phi),
                                w0: 0,
                                n: fnn.l,
                            },
                        ];
                        t2_lin(f, &aff, &runs)?;
                        self.n_x4_laid += 1;
                    }
                }
            }
        }
        for fnn in &funs {
            if fnn.m < 0 || fnn.m as usize >= self.nm || (fnn.tree != 0 && fnn.tree != 2) {
                return Err(Refusal::internal(&format!("internal-t2f-functional-{}", fnn.name)));
            }
        }
        for e in 0..2 {
            for &c in &rd_u[e] {
                if !c {
                    return Err(Refusal::internal(&format!("{}internal-f-table-read", f.g)));
                }
            }
        }
        // Sorted by first entry, the tables must follow each other without gap or overlap.
        let mut nsg_sum = 0usize;
        for un in [0u32, 2u32] {
            let mut iv: Vec<(u64, u64, u64)> = Vec::new();
            for fnn in &funs {
                if fnn.tree == un {
                    let m = &self.mats[fnn.m as usize];
                    iv.push((fnn.at, m.k * (m.m / fnn.l), m.m / fnn.l));
                }
            }
            iv.sort();
            let mut at = self.tab_first[(un / 2) as usize];
            for x in &iv {
                if x.1 == 0 {
                    return Err(Refusal::internal(&format!("{}internal-t2f-table-outside", f.g)));
                }
                if x.0 < at {
                    return Err(Refusal::internal(&format!("{}internal-t2f-tables-overlap", f.g)));
                }
                if x.0 > at {
                    return Err(Refusal::internal(&format!("{}internal-f-tables-gap", f.g)));
                }
                at += x.1;
                nsg_sum += x.2 as usize;
            }
            if at != self.tab_first[(un / 2) as usize] + self.tab_len[(un / 2) as usize] {
                return Err(Refusal::internal(&format!("{}internal-f-tables-gap", f.g)));
            }
            if self.ix.u[un as usize] >= 0 && at > self.n_u[un as usize] {
                return Err(Refusal::internal(&format!("{}internal-t2f-table-outside", f.g)));
            }
        }
        {
            let mut ties = 0usize;
            for t in 0..f.trees.len() {
                let sym = f.trees[t].kind == TreeKind::P;
                if self.ties_on[t] != if sym { 1 } else { 0 } {
                    return Err(Refusal::internal(&format!("{}internal-f-exist", f.g)));
                }
                ties += self.ties_on[t] as usize;
            }
            if ties != self.nm || self.n_x4_laid != nsg_sum {
                return Err(Refusal::internal(&format!("{}internal-f-exist", f.g)));
            }
            for mu in 0..self.nm {
                for nu in mu + 1..self.nm {
                    if self.tie_obj[mu] == self.tie_obj[nu]
                        || self.gt_tree[mu] == self.gt_tree[nu]
                    {
                        return Err(Refusal::internal(&format!("{}internal-f-exist", f.g)));
                    }
                }
            }
        }
        self.ls_tail = f.ls[self.slot_a as usize..self.slot_b as usize].to_vec();
        Ok(())
    }

    /// `linJoin9`: the forest's join, one linear claim on both calls.
    fn lin_join9(&mut self, f: &mut HFork) -> Result<()> {
        for q in 0..2 {
            if self.f9.pad_values[q] != 0 {
                return Err(Refusal::internal(&format!("{}internal-f-padding-key", f.g)));
            }
        }
        let mut ec: Vec<Vec<E>> = Vec::new();
        let mut runs: Vec<Run2<'_>> = Vec::new();
        let mut a = Aff::default();
        for q in 0..2 {
            let c = &self.z[1 + q];
            a.c = a.c + self.f9.e[q] * (self.f9.alpha - es(self.f9.theta, q as u64));
            for p in &c.pc {
                // zrOf(c, p) + p.a, of length log2(CP): the piece's equality factors over its
                // rows. Since b = a + log2(CP), this is zk[n - log2(CP) .. n].
                let len = ceil_log2(p.c_p) as usize;
                let zr = &c.c.zk[(c.c.n as usize) - len..];
                ec.push(eq_tab(zr, len));
            }
        }
        {
            let ey = eq_tab(&self.f9.zy, self.f9.r_k as usize);
            for y in self.f9.nt as usize..(1usize << self.f9.r_k) {
                a.c = a.c + ey[y] * (self.f9.alpha - self.f9.pad_key(0));
            }
        }
        // Padding is described twice: the counts and the places the key forms read.
        let mut read = vec![0u64; self.f9.nt as usize];
        let mut at = 0usize;
        for q in 0..2 {
            let c = &self.z[1 + q];
            for p in &c.pc {
                let r = Run2 {
                    tree: p.tree as u32,
                    row: p.row as u32,
                    first: p.c0,
                    // eqOne(zk, n - b, off >> b): the whole point, only its first n - b bits.
                    coef: E::zero()
                        - self.f9.e[q] * eq_one(&c.c.zk, c.c.n - p.b, p.off >> p.b)?,
                    w: Some(&ec[at]),
                    w0: 0,
                    // The run covers the data columns `Cp`, not the rounded window `CP`.
                    n: p.cp,
                };
                runs.push(r);
                for rr in 0..p.rp {
                    let mut first = p.off + rr * p.c_p;
                    let mut left = p.cp;
                    while left != 0 {
                        let b = first >> self.f9.d_t;
                        let take = left.min(((b + 1) << self.f9.d_t) - first);
                        if b >> self.f9.iota[q] != 0 {
                            return Err(Refusal::internal(&format!("{}internal-f-join-place", f.g)));
                        }
                        read[(self.f9.first[q] as u64 + b) as usize] += take;
                        first += take;
                        left -= take;
                    }
                }
                at += 1;
            }
        }
        {
            let mut laid = vec![0u64; self.f9.nt as usize];
            for y in 0..self.f9.nt as usize {
                if read[y] > 1u64 << self.f9.d_t {
                    return Err(Refusal::internal(&format!("{}internal-f-join-place", f.g)));
                }
                laid[y] = (1u64 << self.f9.d_t) - read[y];
            }
            forest_padding_laid(&self.f9, &laid)?;
        }
        self.join_obj9 = f.n_claim;
        t2_lin(f, &(a - self.f9.c_end.clone()), &runs)?;
        forest_join_added(&self.f9)?;
        Ok(())
    }

    /// `linBits9`: three claims on the planes, the multiplicities' bits in BZ.
    fn lin_bits9(&mut self, f: &mut HFork) -> Result<()> {
        let kb = self.bz_columns();
        let bz_tree = self.ix.bz as u32;
        let l = self.f9.k_t + self.f9.c_k;
        let w0 = eq_tab(&self.f9.zb[0][5..], l as usize);
        let w1 = eq_tab(&self.f9.zb[1][5..], l as usize);
        self.bit_factor9 = self.f9.leaves.eps * self.f9.leaves_a;
        let c0 = psc_row(f, &mut self.f9.leaves, E::one(), &Aff::default())?;
        t2_lin(f, &c0, &[bit_row(bz_tree, kb, 0, self.bit_factor9, &w0)])?;
        t2_lin(
            f,
            &Aff::slot(self.f9.s_bit),
            &[bit_row(bz_tree, kb, 1, E::zero() - E::one(), &w1)],
        )?;
        let w: Vec<E> = (0..kb).map(|u| eb(1u64 << (u & 31))).collect();
        let c2 = Aff::constant(E::zero() - eb((1u64 << self.f9.v()) - self.f9.padding()));
        t2_lin(f, &c2, &[bit_row(bz_tree, kb, 2, E::one(), &w)])?;
        forest_planes_added(&self.f9)?;
        Ok(())
    }

    /// `selfTestF`: checks, once all claims are added, that no column meant to be read has weight 0.
    pub fn self_test(&self, f: &HFork, n_u: [u64; 3]) -> Result<()> {
        let need = |t: i32, r: u32, c: u64| -> Result<()> {
            if f.trees[t as usize].rows[r as usize].l[c as usize].is_zero() {
                return Err(Refusal::internal(&format!(
                    "{}internal-t2f-untyped-{}",
                    f.g, f.trees[t as usize].name
                )));
            }
            Ok(())
        };
        for n in 0..3 {
            if self.ix.u[n] >= 0 {
                let kw = f.trees[self.ix.u[n] as usize].k;
                for x in 0..n_u[n] {
                    need(self.ix.u[n], (x / kw) as u32, x % kw)?;
                }
            }
        }
        let blocks = self.zz_blocks() as u32;
        let reads = self.zz_row_reads();
        let ties = self.zz_row_ties();
        for c in 0..self.mz {
            for b in 0..blocks {
                need(self.ix.zz, b, c)?;
                need(self.ix.zz, blocks + b, self.mz + c)?;
            }
            need(self.ix.zz, reads, c)?;
            need(self.ix.zz, reads, self.mz + c)?;
            need(self.ix.zz, ties, c)?;
            need(self.ix.zz, ties, self.mz + c)?;
        }
        for x in 0..self.bz_columns() {
            need(self.ix.bz, 0, x)?;
            need(self.ix.bz, 1, x)?;
            need(self.ix.bz, 2, x)?;
        }
        for mu in 0..self.nm {
            for c in 0..self.shp[mu].j * self.shp[mu].k {
                need(self.gt_tree[mu] as i32, 0, c)?;
            }
        }
        if self.ls_tail.len() != (self.slot_b - self.slot_a) as usize {
            return Err(Refusal::internal(&format!("{}internal-f-tail-slot", f.g)));
        }
        for j in self.slot_a..self.slot_b {
            if f.ls[j as usize] != self.ls_tail[(j - self.slot_a) as usize] {
                return Err(Refusal::internal(&format!("{}internal-f-tail-slot", f.g)));
            }
        }
        Ok(())
    }

    /// `symShapesHeldF`: the plan's recorded shapes must be the ones in use.
    fn sym_shapes_held(&self, f: &HFork, t: &Tail2) -> Result<()> {
        if self.shape_rec.len() != self.nm {
            return Err(Refusal::internal(&format!("{}internal-sym-shape", f.g)));
        }
        for mu in 0..self.nm {
            let n = &t.nt[self.gt_tree[mu] as usize];
            if !n.p || !n.shape.same(&self.shape_rec[mu]) || !self.shp[mu].same(&self.shape_rec[mu]) {
                return Err(Refusal::internal(&format!("{}internal-sym-shape", f.g)));
            }
        }
        Ok(())
    }

    /// `tileSelfTestF`: the tiling self-test. Call it after [`Self::coefficients`].
    pub fn tile_self_test(&self, f: &HFork, tail: &Tail2) -> Result<()> {
        let bad = || Refusal::internal(&format!("{}internal-t2f-untiled", f.g));
        let mut want: Vec<(i32, usize, i32, &'static str, i32, u64, u64, u64, u64)> = Vec::new();
        let rows1 = 1u64 << (63 - (self.tau as u64).leading_zeros());
        let rows2 = self.tau as u64 - rows1;
        let nb_w: usize = if rows2 != 0 { 2 } else { 1 };
        if rows2 & rows2.wrapping_sub(1) != 0 {
            return Err(bad());
        }
        for q in 0..2i32 {
            want.push((
                q,
                0,
                self.ix.zz,
                "ZZ",
                q * nb_w as i32,
                0,
                rows1,
                (q as u64) * self.mz,
                self.mz,
            ));
            if rows2 != 0 {
                want.push((
                    q,
                    1,
                    self.ix.zz,
                    "ZZ",
                    q * nb_w as i32 + 1,
                    rows1,
                    rows2,
                    (q as u64) * self.mz,
                    self.mz,
                ));
            }
        }
        let cs = [1usize, 2usize];
        let cn = ["R10z", "R8d"];
        let ck = [10i32, 8i32];
        let jo = self.join_obj9;
        if jo == u32::MAX {
            return Err(bad());
        }
        if !self.z[0].pc.is_empty()
            || !self.z[3].pc.is_empty()
            || f.trees[self.ix.zz as usize].rows.len() != 2 * nb_w + 2
            || f.trees[self.ix.bz as usize].rows.len() != 3
        {
            return Err(bad());
        }
        // The lookup forest f9's numbers, recomputed without forest_shape.
        let mut ew = [E::zero(), E::zero()];
        {
            let n9 = self.z[1].c.n;
            let dw = n9.min(self.lidb);
            let io = n9 - dw;
            if self.z[2].c.n != n9
                || self.f9.d_t != dw
                || self.f9.k_t != 10
                || self.f9.nt != (1 << (io + 1))
                || self.f9.r_k != io + 1
                || self.f9.iota != vec![io, io]
                || self.f9.first != vec![0, 1 << io]
                || self.f9.zy.len() as i32 != io + 1
                || self.f9.zx.len() as i32 != dw
                || self.f9.e.len() != 2
            {
                return Err(bad());
            }
            ew[0] = E::one() - self.f9.zy[0];
            ew[1] = self.f9.zy[0];
            if self.f9.e[0] != ew[0] || self.f9.e[1] != ew[1] {
                return Err(bad());
            }
            for q in 1..=2 {
                if self.z[q].c.zk.len() as i32 != n9 || self.z[q].c.alpha != self.f9.alpha {
                    return Err(bad());
                }
                for i in 0..n9 as usize {
                    let expect = if (i as i32) < io { self.f9.zy[1 + i] } else { self.f9.zx[i - io as usize] };
                    if self.z[q].c.zk[i] != expect {
                        return Err(bad());
                    }
                }
            }
        }
        // Each call's constants, and its pieces' key ranges.
        for q in 0..2 {
            let c = &self.z[cs[q]].c;
            let pc = &self.z[cs[q]].pc;
            if c.name != cn[q]
                || c.func != 0
                || c.k != ck[q]
                || c.kappa != 5
                || c.t0 != 0
                || pc.len() != nb_w
                || c.n < 10
                || c.n > 44
                || c.zk.len() as i32 != c.n
            {
                return Err(bad());
            }
            let mut tot = 0u64;
            for p in pc {
                if p.rp == 0
                    || p.cp == 0
                    || p.a < 0
                    || p.a > 40
                    || (1u64 << p.a) != p.rp
                    || p.r0 & (p.rp - 1) != 0
                    || p.c_p < p.cp
                    || p.c_p & (p.c_p - 1) != 0
                    || p.b != p.a + ceil_log2(p.c_p) as i32
                    || p.b > c.n
                {
                    return Err(bad());
                }
                if p.off & ((1u64 << p.b) - 1) != 0 || p.off + (1u64 << p.b) > (1u64 << c.n) {
                    return Err(bad());
                }
                tot += 1u64 << p.b;
            }
            if nb_w == 2 {
                let (a, b) = (&pc[0], &pc[1]);
                if a.off < b.off + (1u64 << b.b) && b.off < a.off + (1u64 << a.b) {
                    return Err(bad());
                }
            }
            let ltot = ceil_log2(tot) as i32;
            if c.n != if ltot < 10 { 10 } else { ltot }
                || c.iota != if c.n > self.lidb { c.n - self.lidb } else { 0 }
            {
                return Err(bad());
            }
        }
        let mut area = 0u128;
        for (x, w) in want.iter().enumerate() {
            let p = &self.z[cs[w.0 as usize]].pc[w.1];
            if w.2 < 0 || w.2 as usize >= f.trees.len() || f.trees[w.2 as usize].name != w.3 {
                return Err(bad());
            }
            if p.tree != w.2
                || p.row != w.4
                || p.r0 != w.5
                || p.rp != w.6
                || p.c0 != w.7
                || p.cp != w.8
            {
                return Err(bad());
            }
            if w.5 + w.6 > f.trees[w.2 as usize].r || w.7 + w.8 > f.trees[w.2 as usize].k {
                return Err(bad());
            }
            area += (w.6 as u128) * (w.8 as u128);
            for y2 in x + 1..want.len() {
                let o = &want[y2];
                if w.5 < o.5 + o.6 && o.5 < w.5 + w.6 && w.7 < o.7 + o.8 && o.7 < w.7 + w.8 {
                    return Err(bad());
                }
            }
        }
        if area != (f.trees[self.ix.zz as usize].r as u128) * (f.trees[self.ix.zz as usize].k as u128)
            || f.trees[self.ix.zz as usize].r != self.tau as u64
            || f.trees[self.ix.zz as usize].k != 2 * self.mz
        {
            return Err(bad());
        }
        // The join's weights.
        for w in &want {
            let c = &self.z[cs[w.0 as usize]].c;
            let pc = &self.z[cs[w.0 as usize]].pc[w.1];
            let tree = &f.trees[w.2 as usize];
            let cv = &tree.rows[w.4 as usize].coef;
            let l = &tree.rows[w.4 as usize].l;
            if cv.len() != tree.r as usize || l.len() != tree.k as usize {
                return Err(bad());
            }
            let ka = t2f_kappa_by_text(f.theta, jo) * ew[w.0 as usize];
            let mk = E::zero() - ka;
            let zk = &c.zk;
            let n = c.n;
            if ka.is_zero() || cv[w.5 as usize].is_zero() || l[w.7 as usize].is_zero() {
                return Err(bad());
            }
            let mut eq = EqRun::new(zk, n, pc.off, E::one());
            for cc in 0..w.8 {
                let v = mk * eq.at();
                if v.is_zero() || cv[w.5 as usize] * l[w.7 as usize + cc as usize] != v {
                    return Err(bad());
                }
                eq.next();
            }
            for r in 0..w.6 {
                let v = mk * eq_at_key(zk, n, pc.off + r * pc.c_p);
                if v.is_zero() || cv[w.5 as usize + r as usize] * l[w.7 as usize] != v {
                    return Err(bad());
                }
            }
            if cv[w.5 as usize + w.6 as usize - 1] * l[w.7 as usize + w.8 as usize - 1]
                != mk * eq_at_key(zk, n, pc.off + (w.6 - 1) * pc.c_p + (w.8 - 1))
            {
                return Err(bad());
            }
            for r in 0..tree.r as usize {
                if (r < w.5 as usize || r >= (w.5 + w.6) as usize) && !cv[r].is_zero() {
                    return Err(bad());
                }
            }
            for cc in 0..tree.k as usize {
                if (cc < w.7 as usize || cc >= (w.7 + w.8) as usize) && !l[cc].is_zero() {
                    return Err(bad());
                }
            }
        }
        // The ties' weights.
        let bad_t = || Refusal::internal(&format!("{}internal-f-tie-weights", f.g));
        {
            let c4 = &f.trees[self.ix.zz as usize].rows[2 * nb_w].coef;
            let c5 = &f.trees[self.ix.zz as usize].rows[2 * nb_w + 1].coef;
            if c4.len() != self.tau as usize || c5.len() != self.tau as usize {
                return Err(bad_t());
            }
            for u in 0..self.tau as usize {
                if c4[u] != f.theta.pow(u as u64) || c5[u] != c4[u] {
                    return Err(bad_t());
                }
            }
        }
        let l5 = &f.trees[self.ix.zz as usize].rows[2 * nb_w + 1].l;
        let mut xi2 = vec![E::zero(); self.tau as usize];
        let mut vt2 = vec![E::zero(); self.tau as usize];
        for u in 0..self.tau as usize {
            xi2[u] = f.theta.pow(u as u64);
            vt2[u] = xi2[u];
        }
        if self.gam_x.len() != self.nm || self.gam_v.len() != self.nm {
            return Err(bad_t());
        }
        let mut cols_seen = 0u64;
        for mu in 0..self.nm {
            let s = self.shp[mu].clone();
            let x = &f.trees[self.gt_tree[mu] as usize];
            if x.kind != TreeKind::P
                || x.rows.len() != 1
                || x.r != s.rr
                || x.k != s.kc
                || self.tie_obj[mu] == u32::MAX
            {
                return Err(bad_t());
            }
            let mut np2 = 1u64;
            while np2 < self.tau as u64 {
                np2 *= 2;
            }
            let mut first2 = 0u64;
            for nu in 0..mu {
                let mut span = 1u64;
                while span < (self.mats[nu].m + 2) / 3 {
                    span *= 2;
                }
                first2 += np2 * span;
            }
            let ka = f.theta.pow(f.plan_claims as u64 + first2);
            let ms2 = (self.mats[mu].m + 2) / 3;
            if ms2 != s.m_s
                || s.j != 1
                || s.r != ms2
                || s.rr != ms2
                || s.rd != 0
                || s.k != self.mats[mu].k
                || s.k1 != s.k
                || s.kc != s.k
                || self.row_x[mu].len() != ms2 as usize
                || self.lo_x[mu].len() != 1
                || self.lo_x[mu][0] != E::one()
                || self.tie_obj[mu] >= f.plan_claims
            {
                return Err(Refusal::internal(&format!("{}internal-sym-rowvec", f.g)));
            }
            let mut hi = vec![E::zero(); ms2 as usize];
            for r in 0..ms2 as usize {
                hi[r] = f.theta.pow(np2 * r as u64);
            }
            let bad_r = || Refusal::internal(&format!("{}internal-sym-rowvec", f.g));
            let ce = &x.rows[0].coef;
            if ce.len() != s.rr as usize {
                return Err(bad_r());
            }
            for r in 0..s.r as usize {
                if ce[r] != hi[r] || ce[r].is_zero() {
                    return Err(bad_r());
                }
            }
            {
                let mut v: Vec<[u64; 3]> = Vec::new();
                for r in 0..s.r as usize {
                    v.push([ce[r].0[0].0, ce[r].0[1].0, ce[r].0[2].0]);
                }
                v.sort();
                for r in 1..v.len() {
                    if v[r] == v[r - 1] {
                        return Err(bad_r());
                    }
                }
            }
            let c0 = self.off[mu];
            let c1 = self.mz + self.off[mu];
            for is in 0..s.m_s {
                let mut v = ka * hi[is as usize];
                for l in 0..3u64 {
                    if 3 * is + l >= s.m {
                        break;
                    }
                    if v.is_zero()
                        || l5[(c0 + 3 * is + l) as usize] != v
                        || l5[(c1 + 3 * is + l) as usize] != es(v, 1u64 << T2D0)
                    {
                        return Err(bad_t());
                    }
                    v = es(v, 1u64 << LRAD);
                }
            }
            cols_seen += s.m;
            let bad_w = || Refusal::internal(&format!("{}internal-sym-weight", f.g));
            let lx = &x.rows[0].l;
            if lx.len() != s.k as usize {
                return Err(bad_w());
            }
            let mka = E::zero() - ka;
            for c in 0..s.k as usize {
                let mut before = 0u64;
                for nu in 0..mu {
                    before += self.mats[nu].k;
                }
                let mut g = E::zero();
                let mut gv = E::zero();
                for u in 0..self.tau as usize {
                    let xcf = self.cf[((before + c as u64) * self.tau as u64 + u as u64) as usize];
                    if xcf != 0 {
                        g = if xcf < 0 { g - xi2[u] } else { g + xi2[u] };
                        gv = if xcf < 0 { gv - vt2[u] } else { gv + vt2[u] };
                    }
                }
                if self.gam_x[mu].len() != s.k as usize
                    || self.gam_v[mu].len() != s.k as usize
                    || self.gam_x[mu][c] != g
                    || self.gam_v[mu][c] != gv
                {
                    return Err(Refusal::internal(&format!("{}internal-f-fold-array", f.g)));
                }
                if lx[c] != mka * g {
                    return Err(bad_w());
                }
            }
        }
        if cols_seen != self.mz || l5.len() != 2 * self.mz as usize {
            return Err(bad_t());
        }
        // The reads' weights on ZZ.
        let bad_q = || Refusal::internal(&format!("{}internal-f-read-weights", f.g));
        {
            let l4 = &f.trees[self.ix.zz as usize].rows[2 * nb_w].l;
            if self.fun_laid.is_empty() || l4.len() != 2 * self.mz as usize {
                return Err(bad_q());
            }
            let mut np2 = 1u64;
            while np2 < self.tau as u64 {
                np2 *= 2;
            }
            let mut first_r = 0u64;
            for nu in 0..self.nm {
                let mut span = 1u64;
                while span < (self.mats[nu].m + 2) / 3 {
                    span *= 2;
                }
                first_r += np2 * span;
            }
            let by_step = f.theta.pow(np2);
            let mut want_w = vec![E::zero(); 2 * self.mz as usize];
            let mut q = 0usize;
            let mut before = 0u64;
            for mu in 0..self.nm {
                for un in [0u32, 2u32] {
                    for fnn in self.fun_laid.clone() {
                        if fnn.m < 0 || fnn.m as usize != mu || fnn.tree != un {
                            continue;
                        }
                        let m = self.mats[mu].m;
                        let at = before;
                        if m == 0 || fnn.l == 0 || m % fnn.l != 0 || fnn.phi.len() as u64 != fnn.l {
                            return Err(bad_q());
                        }
                        let nsg = m / fnn.l;
                        let mut kr = vec![E::zero(); nsg as usize];
                        kr[0] = f.theta.pow(f.plan_claims as u64 + first_r + q as u64 * np2);
                        for sg in 1..nsg as usize {
                            kr[sg] = kr[sg - 1] * by_step;
                        }
                        for x in 0..m as usize {
                            let v = kr[x / fnn.l as usize] * fnn.phi[x % fnn.l as usize];
                            let lo = (at + x as u64) as usize;
                            let hi = (self.mz + at + x as u64) as usize;
                            want_w[lo] = want_w[lo] + v;
                            want_w[hi] = want_w[hi] + es(v, 1u64 << T2D0);
                        }
                        q += nsg as usize;
                    }
                }
                before += self.mats[mu].m;
            }
            if q != self.n_x4_laid || before != self.mz {
                return Err(bad_q());
            }
            for x in 0..2 * self.mz as usize {
                if l4[x] != want_w[x] {
                    return Err(bad_q());
                }
            }
        }
        // BZ's weights.
        let bad_b = || Refusal::internal(&format!("{}internal-f-bz-weights", f.g));
        let b = &f.trees[self.ix.bz as usize];
        if b.r != 32 || b.k != self.bz_columns() {
            return Err(bad_b());
        }
        for r in 0..32 {
            if b.rows[2].coef[r] != E::one() {
                return Err(bad_b());
            }
        }
        {
            let l_kb = self.f9.k_t + self.f9.c_k;
            if self.f9.nc != 2 || self.f9.c_k != 1 || b.k != (1u64 << l_kb) {
                return Err(bad_b());
            }
            for e in 0..2 {
                let cv = &b.rows[e].coef;
                let l = &b.rows[e].l;
                if cv.len() != 32
                    || l.len() != b.k as usize
                    || self.f9.zb[e].len() as i32 != 5 + l_kb
                {
                    return Err(bad_b());
                }
                for r in 0..32 {
                    if cv[r] != super::packing::eq_plain_f(&self.f9.zb[e], 5, r as u64) {
                        return Err(bad_b());
                    }
                }
                let mk = t2f_kappa_by_text(f.theta, jo + 1 + e as u32)
                    * if e != 0 { E::zero() - E::one() } else { self.bit_factor9 };
                let mut st = super::packing::UnscaledEqIterator::new(&self.f9.zb[e][5..], l_kb, 0);
                for x in 0..b.k as usize {
                    if l[x] != mk * st.at() {
                        return Err(bad_b());
                    }
                    st.next();
                }
            }
            let kp = t2f_kappa_by_text(f.theta, jo + 3);
            if b.rows[2].l.len() != b.k as usize {
                return Err(bad_b());
            }
            for x in 0..b.k as usize {
                if b.rows[2].l[x] != es(kp, 1u64 << (x & 31)) {
                    return Err(bad_b());
                }
            }
        }
        if !tail.link {
            return Err(Refusal::internal(&format!("{}internal-sym-shape", f.g)));
        }
        self.sym_shapes_held(f, tail)?;
        Ok(())
    }

    /// `borderMeans`: records which tree `PF_i` is.
    pub fn border_means(&mut self, i_f: usize, owner_no: i32, index: i32) -> Result<()> {
        if i_f >= self.pl_for.len() || self.pl_for[i_f].owner >= 0 || owner_no < 0 || index < 0 {
            return Err(Refusal::internal("internal-border-count"));
        }
        self.pl_for[i_f].owner = owner_no;
        self.pl_for[i_f].root_index = index;
        Ok(())
    }

    /// `ownerIs(no)`.
    pub fn owner_is(&mut self, no: i32) {
        for pl in &mut self.pl_own {
            pl.owner = no;
        }
    }

    /// `ownEntry(role)`: the owner's placement record of the matrix named "qa" (role `"qa"`) or
    /// "xbO" (any other role).
    pub fn own_entry(&self, role: &str) -> Result<&PlaceF> {
        let want = if role == "qa" { "qa" } else { "xbO" };
        for i in 0..self.px_mat.len() {
            if self.mats[self.px_mat[i]].name == want {
                if !self.pl_own[i].whole() {
                    return Err(Refusal::internal("internal-border-count"));
                }
                return Ok(&self.pl_own[i]);
            }
        }
        Err(Refusal::internal("internal-border-count"))
    }
}

/// One of `linBits9`'s three claims: a run over `BZ`'s row.
fn bit_row(bz_tree: u32, kb: u64, row: u32, coef: E, w: &[E]) -> Run2<'_> {
    Run2 { tree: bz_tree, row, first: 0, coef, w: Some(w), w0: 0, n: kb }
}

/// `eqAtKey(zp, n, idx)`: `eq(zp, idx)` for the self-test.
fn eq_at_key(zp: &[E], n: i32, idx: u64) -> E {
    let mut p = E::one();
    for v in 0..n as usize {
        p = p * if (idx >> (n as usize - 1 - v)) & 1 != 0 { zp[v] } else { E::one() - zp[v] };
    }
    p
}

/// `funDigest`: hashes five fields of every functional with `mix64`; it guards against a bug in
/// this program, not against an adversary.
fn fun_digest(fun: &[super::lookup::HFun], out: &mut [u32; 8]) {
    let mut d = vec![0u64; fun.len()];
    for (i, f) in fun.iter().enumerate() {
        let mut h = mix64(0x4631_3846 + i as u64);
        for v in [
            f.m as i64 as u64,
            f.l,
            f.tree as u64,
            f.at,
            f.phi.len() as u64,
        ] {
            h = mix64(h.wrapping_add(v));
        }
        let mut c = [0u64; 3];
        for k in 0..3 {
            c[k] = mix64(h.wrapping_add(k as u64));
        }
        for x in &f.phi {
            for k in 0..3 {
                c[k] = mix64(c[k].wrapping_add(x.0[k].0));
            }
        }
        for k in 0..3 {
            h = mix64(h.wrapping_add(c[k]));
        }
        d[i] = h;
    }
    let mut a = mix64(fun.len() as u64);
    let mut b = mix64(!(fun.len() as u64));
    for v in d {
        a = mix64(a.wrapping_add(v));
        b = mix64(b ^ v);
    }
    *out = [0; 8];
    out[0] = a as u32;
    out[1] = (a >> 32) as u32;
    out[2] = b as u32;
    out[3] = (b >> 32) as u32;
}

/// `unused` imports kept for callers of this module.
pub use super::segment::{eq_low, eq_low_at};
