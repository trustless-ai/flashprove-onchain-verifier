//! Multilinear-polynomial helpers, ported from `blocks/field/mle.h`.
//!
//! Variable t goes with bit t of an index, and bit 0 is the least significant.
//! `eq(j, z) = prod_t (z[t] if bit t of j is 1, else 1 - z[t])`.
//! Array lengths are checked as C++'s `BLK_REQUIRE` does; a violation is a program fault.

use alloc::vec;
use alloc::vec::Vec;

use super::ext::{F, E};

/// out[j] = eq(j, z) for all j < 2^k (`eq_table`).
pub fn eq_table(z: &[E], k: usize, out: &mut [E]) {
    assert!(k < 64 && out.len() >= (1usize << k), "eq_table: output too short");
    out[0] = E::one();
    for t in 0..k {
        let half = 1usize << t;
        for j in 0..half {
            let hi = out[j] * z[t];
            out[j + half] = hi;
            out[j] = out[j] - hi;
        }
    }
}

/// eq(j, z) for one index; bits of j from bit k up are ignored (`eq_index`).
pub fn eq_index(j: u64, z: &[E], k: usize) -> E {
    let mut r = E::one();
    for t in 0..k {
        r = r
            * if (j >> t) & 1 != 0 {
                z[t]
            } else {
                E::one() - z[t]
            };
    }
    r
}

/// prod_t (a[t] b[t] + (1 - a[t]) (1 - b[t])) (`eq_eval`).
pub fn eq_eval(a: &[E], b: &[E], k: usize) -> E {
    let mut r = E::one();
    for t in 0..k {
        let ab = a[t] * b[t];
        r = r * (ab + ab + E::one() - a[t] - b[t]);
    }
    r
}

/// coeff[0] + coeff[1] x + .. + coeff[d - 1] x^(d - 1); 0 for d = 0 (`poly_eval`).
pub fn poly_eval(coeff: &[E], d: usize, x: E) -> E {
    let mut r = E::zero();
    let mut i = d;
    while i > 0 {
        i -= 1;
        r = r * x + coeff[i];
    }
    r
}

/// (1 - g) a + g b for base-field inputs (`fold_pair(F, F, E)`).
#[inline]
pub fn fold_pair_f(a: F, b: F, g: E) -> E {
    g * (b - a) + a
}

/// (1 - g) a + g b for extension-field inputs (`fold_pair(E, E, E)`).
#[inline]
pub fn fold_pair_e(a: E, b: E, g: E) -> E {
    a + g * (b - a)
}

/// A scalar that `mle_eval` can lift into E.
pub trait MleScalar: Copy {
    fn zero() -> Self;
    fn to_e(self) -> E;
    fn from_e_mul(self, e: E) -> E;
}

impl MleScalar for F {
    #[inline]
    fn zero() -> Self {
        F::zero()
    }
    #[inline]
    fn to_e(self) -> E {
        E::from_base(self)
    }
    #[inline]
    fn from_e_mul(self, e: E) -> E {
        e * self
    }
}

impl MleScalar for E {
    #[inline]
    fn zero() -> Self {
        E::zero()
    }
    #[inline]
    fn to_e(self) -> E {
        self
    }
    #[inline]
    fn from_e_mul(self, e: E) -> E {
        e * self
    }
}

#[inline]
fn fold_pair_t<T: MleScalar>(a: T, b: T, g: E) -> E {
    g * (b.to_e() - a.to_e()) + a.to_e()
}

/// sum_{j < len} eq(j, z) v[j] for a vector over F or E with len <= 2^k; entries from len on count
/// as zero (`mle_eval`). About len + k products.
pub fn mle_eval<T: MleScalar>(v: &[T], len: usize, z: &[E], k: usize) -> E {
    assert!(k < 64 && len <= (1usize << k), "mle_eval: vector longer than the cube");
    if len == 0 {
        return E::zero();
    }
    if k == 0 {
        return T::zero().to_e() + v[0].to_e();
    }
    let mut a: Vec<E> = vec![E::zero(); (len + 1) / 2];
    for j in 0..a.len() {
        a[j] = if 2 * j + 1 < len {
            fold_pair_t(v[2 * j], v[2 * j + 1], z[0])
        } else {
            (E::one() - z[0]) * v[2 * j].to_e()
        };
    }
    let mut m = a.len();
    for t in 1..k {
        let h = (m + 1) / 2;
        for j in 0..h {
            a[j] = if 2 * j + 1 < m {
                fold_pair_e(a[2 * j], a[2 * j + 1], z[t])
            } else {
                (E::one() - z[t]) * a[2 * j]
            };
        }
        m = h;
    }
    a[0]
}

/// Writes the first `len` entries of the product form to `out` (`product_table`).
pub fn product_table(f: &[F], k: usize, len: usize, out: &mut [F]) {
    assert!(k < 64 && len <= (1usize << k), "product_table: too many entries");
    if len == 0 {
        return;
    }
    out[0] = F::one();
    for t in 0..k {
        let half = 1usize << t;
        let mut j = 0;
        while j < half && j + half < len {
            out[j + half] = out[j] * f[t];
            j += 1;
        }
    }
}

/// Entry j of the product form; bits of j from bit k up are ignored (`product_index`).
pub fn product_index(f: &[F], k: usize, j: u64) -> F {
    let mut r = F::one();
    for t in 0..k {
        if (j >> t) & 1 != 0 {
            r = r * f[t];
        }
    }
    r
}

/// The inner product of a product form with eq(., z): prod_t (1 - z[t] + z[t] f[t])
/// (`product_mle`).
pub fn product_mle(f: &[F], z: &[E], k: usize) -> E {
    let mut r = E::one();
    for t in 0..k {
        r = r * (z[t] * (f[t] - F::one()) + F::one());
    }
    r
}

/// A scalar that `product_dot` can multiply by a base-field factor.
pub trait ProductScalar: Copy {
    fn zero() -> Self;
    fn add(self, o: Self) -> Self;
    fn mul_f(self, f: F) -> Self;
}

impl ProductScalar for F {
    #[inline]
    fn zero() -> Self {
        F::zero()
    }
    #[inline]
    fn add(self, o: Self) -> Self {
        self + o
    }
    #[inline]
    fn mul_f(self, f: F) -> Self {
        self * f
    }
}

impl ProductScalar for E {
    #[inline]
    fn zero() -> Self {
        E::zero()
    }
    #[inline]
    fn add(self, o: Self) -> Self {
        self + o
    }
    #[inline]
    fn mul_f(self, f: F) -> Self {
        self * f
    }
}

/// sum_{j < len} v[j] * (entry j of the product form) (`product_dot`).
pub fn product_dot<T: ProductScalar>(v: &[T], len: usize, f: &[F], k: usize) -> T {
    assert!(k < 64 && len <= (1usize << k), "product_dot: vector longer than the form");
    if len == 0 {
        return T::zero();
    }
    let mut a: Vec<T> = v[..len].to_vec();
    let mut m = len;
    let mut t = 0;
    while t < k && m > 1 {
        let h = (m + 1) / 2;
        for j in 0..h {
            a[j] = if 2 * j + 1 < m {
                a[2 * j].add(a[2 * j + 1].mul_f(f[t]))
            } else {
                a[2 * j]
            };
        }
        m = h;
        t += 1;
    }
    a[0]
}
