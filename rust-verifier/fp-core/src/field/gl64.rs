//! Arithmetic modulo the Goldilocks prime on bare `u64`, ported from
//! `blocks/field/gl64.h`.
//!
//! Unless a comment says otherwise, arguments are canonical words (below `P`) and results are
//! canonical. The reduction follows plonky2's `reduce128`; a final step makes it canonical.

/// p = 2^64 - 2^32 + 1.
pub const P: u64 = 0xFFFF_FFFF_0000_0001;
/// 2^64 mod p.
pub const EPS: u64 = 0xFFFF_FFFF;
/// The length of p in bits.
pub const BITS: u32 = 64;
/// X^3 - NR is irreducible in F[X]; this is the cubic non-residue.
pub const NR: u64 = 2;
/// log2(p), rounded down (`GL64::LOG2_P`).
pub const LOG2_P: f64 = 64.0 - 3.3592e-10;

/// Any word to the canonical word of its class (`GL64::canonical`).
#[inline]
pub const fn canonical(x: u64) -> u64 {
    if x >= P {
        x - P
    } else {
        x
    }
}

/// a + b (`GL64::add`).
#[inline]
pub const fn add(a: u64, b: u64) -> u64 {
    let nb = P.wrapping_sub(b);
    let d = a.wrapping_sub(nb);
    if a < nb {
        d.wrapping_sub(EPS)
    } else {
        d
    }
}

/// a - b (`GL64::sub`).
#[inline]
pub const fn sub(a: u64, b: u64) -> u64 {
    let d = a.wrapping_sub(b);
    if a < b {
        d.wrapping_sub(EPS)
    } else {
        d
    }
}

/// -a, with -0 = 0 (`GL64::neg`).
#[inline]
pub const fn neg(a: u64) -> u64 {
    if a != 0 {
        P - a
    } else {
        0
    }
}

/// The product of any two words as `(hi, lo)` with `hi 2^64 + lo` (`GL64::mul_wide`).
#[inline]
pub const fn mul_wide(a: u64, b: u64) -> (u64, u64) {
    let t = (a as u128) * (b as u128);
    ((t >> 64) as u64, t as u64)
}

/// `hi 2^64 + lo` modulo p, for any two words (`GL64::reduce128`).
#[inline]
pub const fn reduce128(hi: u64, lo: u64) -> u64 {
    let hh = hi >> 32;
    let hl = hi & EPS;
    let mut t = lo.wrapping_sub(hh);
    if lo < hh {
        t = t.wrapping_sub(EPS);
    }
    let m = (hl << 32).wrapping_sub(hl);
    let mut r = t.wrapping_add(m);
    if r < m {
        r = r.wrapping_add(EPS);
    }
    canonical(r)
}

/// a b mod p (`GL64::mul`).
#[inline]
pub const fn mul(a: u64, b: u64) -> u64 {
    let (hi, lo) = mul_wide(a, b);
    reduce128(hi, lo)
}

/// a0 b0 + a1 b1 + a2 b2, reduced once (`GL64::dot3`).
#[inline]
pub const fn dot3(a0: u64, b0: u64, a1: u64, b1: u64, a2: u64, b2: u64) -> u64 {
    let (mut hi, mut lo) = mul_wide(a0, b0);
    let (mut h, l) = mul_wide(a1, b1);
    lo = lo.wrapping_add(l);
    if lo < l {
        h = h.wrapping_add(1);
    }
    hi = hi.wrapping_add(h);
    let mut c = if hi < h { 1u64 } else { 0 };
    let (h2, l2) = mul_wide(a2, b2);
    lo = lo.wrapping_add(l2);
    let h3 = if lo < l2 { h2.wrapping_add(1) } else { h2 };
    hi = hi.wrapping_add(h3);
    if hi < h3 {
        c += 1;
    }
    sub(reduce128(hi, lo), c << 32)
}

/// NR * a, computed as a + a because NR = 2 (`GL64::times_nr`).
#[inline]
pub const fn times_nr(a: u64) -> u64 {
    add(a, a)
}

/// Any word modulo p (`GL64::from_u64`).
#[inline]
pub const fn from_u64(v: u64) -> u64 {
    canonical(v)
}

/// One rejection-sampling step (`GL64::from_word`): the word itself if it is below p.
#[inline]
pub const fn from_word(w: u64) -> Option<u64> {
    if w < P {
        Some(w)
    } else {
        None
    }
}
