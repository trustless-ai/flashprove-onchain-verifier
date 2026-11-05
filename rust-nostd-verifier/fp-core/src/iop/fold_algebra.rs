//! Field arithmetic for FOLD. Ported from `blocks/iop/fold_algebra.h` (lines 33-133).
//!
//! A table of 2^a rows is one vector: entry c of row b is at index b + 2^a c; the low a bits of
//! the index are the row. Folding the first variable at g halves the rows:
//! `v'[i] = (1-g) v[2i] + g v[2i+1]`. Encoding is linear and acts row by row, so it commutes with
//! folding.

use alloc::vec;
use alloc::vec::Vec;

use super::hp::{hp_entries, hp_place, ChallengeField, Weight};

/// Folds the first variable in place (`fold_low_once`, fold_algebra.h:33-38).
pub fn fold_low_once<K: ChallengeField>(v: &mut Vec<K>, g: &K) {
    assert!(v.len() % 2 == 0, "fold_low_once: the table has an odd number of rows");
    for i in 0..v.len() / 2 {
        v[i] = v[2 * i] + *g * (v[2 * i + 1] - v[2 * i]);
    }
    v.truncate(v.len() / 2);
}

/// Folds the first `count` variables at `g[0..count)` (`fold_low`, fold_algebra.h:40-45).
pub fn fold_low<K: ChallengeField>(mut v: Vec<K>, g: &[K], count: u32) -> Vec<K> {
    for j in 0..count as usize {
        fold_low_once(&mut v, &g[j]);
    }
    v
}

/// The three coefficients of `q(X) = <a folded at X, m folded at X>` (`pair_products`,
/// fold_algebra.h:47-61).
pub fn pair_products<K: ChallengeField>(a: &[K], m: &[K]) -> Vec<K> {
    assert!(
        a.len() == m.len() && a.len() % 2 == 0,
        "pair_products: the two tables differ in size, or have an odd number of rows"
    );
    let mut q = vec![K::zero(); 3];
    let mut i = 0usize;
    while i < a.len() {
        let a0 = a[i];
        let a1 = a[i + 1] - a0;
        let m0 = m[i];
        let m1 = m[i + 1] - m0;
        q[0] = q[0] + a0 * m0;
        q[1] = q[1] + a0 * m1 + a1 * m0;
        q[2] = q[2] + a1 * m1;
        i += 2;
    }
    q
}

/// The inner product (`inner`, fold_algebra.h:63-69).
pub fn inner<K: ChallengeField>(a: &[K], b: &[K]) -> K {
    assert!(a.len() == b.len(), "inner: the two vectors differ in length");
    let mut s = K::zero();
    for i in 0..a.len() {
        s = s + a[i] * b[i];
    }
    s
}

/// One `Weight` per variable of FOLD's hiding polynomial (`fold_mask_variables`,
/// fold_algebra.h:71-77).
pub fn fold_mask_variables<K: ChallengeField>(k: u32) -> Vec<Weight<K>> {
    vec![Weight::plain(3); k as usize]
}

/// Columns that `fold_mask_table()` fills (`fold_mask_columns`, fold_algebra.h:79-81). `h <= k`
/// is not checked.
pub fn fold_mask_columns(k: u32, h: u32) -> usize {
    2 * k as usize + 1 - h as usize
}

/// Stores the coefficients `w` (order `hp_place()`) in 2^h rows of length `len`
/// (`fold_mask_table`, fold_algebra.h:83-115).
pub fn fold_mask_table<K: ChallengeField>(k: u32, h: u32, len: usize, w: &[K]) -> Vec<K> {
    assert!(k >= 1 && h <= k, "fold_mask_table: no row variable, or more mask rows than main rows");
    assert!(
        len >= fold_mask_columns(k, h),
        "fold_mask_table: the rows are too short for the coefficients"
    );
    let vars = fold_mask_variables::<K>(k);
    assert!(
        w.len() == hp_entries(&vars),
        "fold_mask_table: the number of coefficients is not 2k + 1"
    );
    let coeff = |l: u32, t: usize| w[hp_place(&vars, l as usize - 1, t)];
    let rows = 1usize << h;
    let mut table = vec![K::zero(); rows * len];
    for b in 0..rows {
        // `at(col)` in the C++ function: table[b + rows * col].
        table[b] = if h < k { coeff(h + 1, 1) } else { coeff(k, 0) };
        let mut l = h;
        while l >= 1 && ((b >> (l - 1)) & 1) != 0 {
            table[b] = table[b] + coeff(l, 1);
            table[b + rows * l as usize] = coeff(l, 2);
            l -= 1;
        }
        let mut col = h + 1;
        for l in h + 1..=k {
            let start = if l == h + 1 { 2 } else { 1 };
            for t in start..=2 {
                table[b + rows * col as usize] = coeff(l, t);
                col += 1;
            }
        }
        if h < k {
            table[b + rows * col as usize] = coeff(k, 0);
        }
    }
    table
}

/// The public weights `u(g)` in the table's column order (`fold_mask_weights`,
/// fold_algebra.h:117-133).
pub fn fold_mask_weights<K: ChallengeField>(k: u32, h: u32, len: usize, g: &[K]) -> Vec<K> {
    assert!(
        k >= 1 && h <= k && g.len() == k as usize,
        "fold_mask_weights: no row variable, more mask rows than main rows, or not one challenge for each variable"
    );
    assert!(
        len >= fold_mask_columns(k, h),
        "fold_mask_weights: the rows are too short for the coefficients"
    );
    let kk = k as usize;
    let hh = h as usize;
    let mut after = vec![K::one(); kk + 1];
    let mut l = kk;
    while l > 0 {
        l -= 1;
        after[l] = after[l + 1] * g[l];
    }
    let mut u = vec![K::zero(); len];
    u[0] = after[hh];
    for l in 1..=hh {
        u[l] = g[l - 1] * after[hh];
    }
    let mut col = hh + 1;
    for l in hh + 1..=kk {
        let start = if l == hh + 1 { 2 } else { 1 };
        for t in start..=2 {
            u[col] = if t == 1 {
                g[l - 1] * after[l]
            } else {
                g[l - 1] * g[l - 1] * after[l]
            };
            col += 1;
        }
    }
    if h < k {
        u[col] = K::one();
    }
    u
}
