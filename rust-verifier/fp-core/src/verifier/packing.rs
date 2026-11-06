//! The approximate range check's packing, placement and tie, ported from
//! `verifier/src/vf_smallness_packing.h`.
//!
//! A symbol, one field element, packs up to three cells at radix `B = 2^20`. A symbol tree
//! (`HTree::kind == P`) is the array of a matrix's symbols. The tie is the linear claim that
//! relates packed cells to the check's random combinations of columns.
//!
//! `refuse()` becomes a [`Refusal`] value. The C++ placement functions divide by `ShP::J` without
//! a check; `J` is 1 for every shape that the programs make (`t2AddP`), so [`place_p`] asserts it
//! rather than defining the C++ zero-divisor case.

use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::E;
use crate::refusal::{Refusal, Result};

/// `LRAD`: the radix is `2^20` (`vf_smallness_packing.h:18`).
pub const LRAD: u32 = 20;
/// `LANES`: cell rows per symbol. Four break (f1).
pub const LANES: usize = 3;
/// `KCAP`: the cap on a matrix's columns (`hid-k-range`).
pub const KCAP: u64 = 8191;
/// `RADB`: `2^LRAD`.
pub const RADB: u64 = 1u64 << LRAD;

/// The shape of a symbol tree (`struct ShP`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ShP {
    pub m: u64,
    pub k: u64,
    /// `mS = m' = ceil(m / 3)` symbol rows.
    pub m_s: u64,
    pub w: i32,
    pub ln: i32,
    pub c_j: i32,
    pub a_x: i32,
    pub t: u32,
    pub a: u32,
    pub n: u64,
    pub mk: u64,
    pub p2: u64,
    pub k1: u64,
    pub kc: u64,
    pub j: u64,
    pub r: u64,
    pub rd: u64,
    pub rr: u64,
}

impl ShP {
    /// `ShP::same`.
    pub fn same(&self, o: &ShP) -> bool {
        self == o
    }
}

/// The placement of one symbol (`struct PlP`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PlP {
    pub row: u64,
    pub place: u64,
}

/// `placeP(s, iS, c)`: the symbol of symbol row `iS` and matrix column `c`. C++ checks neither
/// `iS` nor `c`.
pub fn place_p(s: &ShP, i_s: u64, c: u64) -> PlP {
    assert!(s.j != 0, "place_p: the C++ division by j would be undefined");
    PlP { row: i_s / s.j, place: c * s.j + (i_s % s.j) }
}

/// The placement record of one matrix (`struct PlaceF`). The sentinels of `col0`, `off`,
/// `owner` and `rootIndex` are the C++ initializers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlaceF {
    pub owner: i32,
    pub root_index: i32,
    pub sh: ShP,
    pub have_shape: bool,
    pub col0: u64,
    pub k: u64,
    pub m: u64,
    pub have_matrix: bool,
    pub hb: u32,
    pub m_s: u64,
    pub lanes: u64,
    pub pad_rows: u64,
    pub j: u64,
    pub kk: u64,
    pub off: u64,
    pub w: u32,
}

impl Default for PlaceF {
    fn default() -> Self {
        Self {
            owner: -1,
            root_index: -1,
            sh: ShP::default(),
            have_shape: false,
            col0: u64::MAX,
            k: 0,
            m: 0,
            have_matrix: false,
            hb: 0,
            m_s: 0,
            lanes: 0,
            pad_rows: 0,
            j: 0,
            kk: 0,
            off: u64::MAX,
            w: 0,
        }
    }
}

impl PlaceF {
    /// `PlaceF::whole()`.
    pub fn whole(&self) -> bool {
        self.owner >= 0 && self.root_index >= 0 && self.have_shape && self.have_matrix && self.hb != 0
    }
}

/// `samePlaceF`: the label of the first group of fields in which the owner's record `o` and the
/// reader's `r` differ, or `""`. `"P3"` also covers the owner's columns running past `K`.
pub fn same_place_f(o: &PlaceF, r: &PlaceF) -> &'static str {
    if o.owner != r.owner {
        return "P0";
    }
    if !o.sh.same(&r.sh) {
        return "P1";
    }
    if o.col0 != r.col0 || o.k != r.k || o.col0.wrapping_add(o.k) > o.kk {
        return "P3";
    }
    if o.m != r.m {
        return "P4";
    }
    if o.root_index != r.root_index {
        return "P5";
    }
    if o.hb != r.hb {
        return "P6";
    }
    if o.m_s != r.m_s
        || o.lanes != r.lanes
        || o.pad_rows != r.pad_rows
        || o.j != r.j
        || o.kk != r.kk
        || o.off != r.off
        || o.w != r.w
    {
        return "P9";
    }
    ""
}

/// `eS(x, s)`: `x` times the base-field element `s`.
#[inline]
pub fn e_scale(x: E, s: u64) -> E {
    x * E::from_base(crate::field::ext::F::from_u64(s))
}

/// `tieLeft(s, rows, lo)`: the tie's left coefficients, one per cell row `i < m`.
pub fn tie_left(s: &ShP, rows: &[E], lo: &[E]) -> Result<Vec<E>> {
    if rows.len() != s.rr as usize || lo.len() != s.j as usize {
        return Err(Refusal::internal("internal-sym-point"));
    }
    assert!(s.j != 0, "tie_left: the C++ division by j would be undefined");
    let mut w = vec![E::zero(); s.m as usize];
    for i in 0..s.m_s {
        let e = rows[(i / s.j) as usize] * lo[(i % s.j) as usize];
        let mut sc = 1u64;
        let mut l = 0usize;
        while l < LANES && (LANES as u64) * i + (l as u64) < s.m {
            w[(LANES as u64 * i) as usize + l] = if l == 0 { e } else { e_scale(e, sc) };
            sc <<= LRAD;
            l += 1;
        }
    }
    Ok(w)
}

/// `tieRight(s, lo, gam)`: the tie's right coefficients, of a tree row's first `J * k` entries.
pub fn tie_right(s: &ShP, lo: &[E], gam: &[E]) -> Result<Vec<E>> {
    if lo.len() != s.j as usize || gam.len() != s.k as usize {
        return Err(Refusal::internal("internal-sym-point"));
    }
    let mut w = vec![E::zero(); (s.j * s.k) as usize];
    for c in 0..s.k {
        for x in 0..s.j {
            let p = place_p(s, x, c);
            w[p.place as usize] = gam[c as usize] * lo[x as usize];
        }
    }
    Ok(w)
}

/// `eqPlainF(z, n, idx)`: `eq(z, idx)` as the plain product over `idx`'s `n` bits, the top bit
/// taking `z[0]`. For self-tests only.
pub fn eq_plain_f(z: &[E], n: i32, idx: u64) -> E {
    let mut p = E::one();
    for v in 0..n as usize {
        p = p * if (idx >> (n as usize - 1 - v)) & 1 != 0 { z[v] } else { E::one() - z[v] };
    }
    p
}

/// `UnscaledEqIterator`: `eq(z, idx)` at consecutive `idx`, for the tiling self-test. Only `idx`'s
/// low `n` bits count.
pub struct UnscaledEqIterator {
    z: Vec<E>,
    n: i32,
    idx: u64,
    pre: Vec<E>,
}

impl UnscaledEqIterator {
    /// The C++ constructor `UnscaledEqIterator(z, n, i0)`.
    pub fn new(z: &[E], n: i32, i0: u64) -> Self {
        let mut it = Self { z: z.to_vec(), n, idx: i0, pre: vec![E::zero(); n as usize + 1] };
        it.pre[0] = E::one();
        it.fill(0);
        it
    }

    fn fill(&mut self, v0: i32) {
        for v in v0..self.n {
            let bit = (self.idx >> (self.n - 1 - v)) & 1 != 0;
            let z = self.z[v as usize];
            self.pre[v as usize + 1] =
                self.pre[v as usize] * if bit { z } else { E::one() - z };
        }
    }

    /// `at()`.
    pub fn at(&self) -> E {
        self.pre[self.n as usize]
    }

    /// `next()`.
    pub fn next(&mut self) {
        let ch = self.idx ^ self.idx.wrapping_add(1);
        self.idx = self.idx.wrapping_add(1);
        let top = 63 - ch.leading_zeros() as i32;
        self.fill(if top >= self.n { 0 } else { self.n - 1 - top });
    }
}
