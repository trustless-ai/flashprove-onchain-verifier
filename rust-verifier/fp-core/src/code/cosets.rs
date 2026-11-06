//! Evaluation points and basis factors of the Reed-Solomon code, ported from
//! `blocks/code/cosets.h`.
//!
//! Positions of a code of length `2^log_n` use `2^(log_n - s)` cosets of the subgroup `H` of order
//! `2^s`, `s = min(log_n, 32)`. With the generator 7 and `w = GL64_ROOT_32`, position `I` has the
//! point `7^(1 + c) * prod_{i < s, bit i of I} w^(2^(31 - i))`, `c = I >> s`.
//! `tau = 1` in the C++ comment's notation (`7^0 = 1`): the point is never 0.

use alloc::vec;
use alloc::vec::Vec;

use crate::field::gl64;

pub const GL64_GENERATOR: u64 = 7;
pub const GL64_ROOT_32: u64 = 0xE2AF_7063_5744_FD26;
pub const GL64_SUBGROUP_LOG: u32 = 32;
pub const GL64_MOST_LOG_N: u32 = 60;

#[inline]
pub fn gl64_subgroup_log(log_n: u32) -> u32 {
    if log_n < GL64_SUBGROUP_LOG { log_n } else { GL64_SUBGROUP_LOG }
}

#[inline]
pub fn gl64_pow(mut a: u64, mut e: u64) -> u64 {
    let mut r = 1u64;
    while e != 0 {
        if e & 1 != 0 {
            r = gl64::mul(r, a);
        }
        e >>= 1;
        a = gl64::mul(a, a);
    }
    r
}

/// The point `z_I` of position `I`.
#[inline]
pub fn gl64_point(log_n: u32, position: u64) -> u64 {
    let s = gl64_subgroup_log(log_n);
    let mut z = gl64_pow(GL64_GENERATOR, 1 + (position >> s));
    let mut root = GL64_ROOT_32;
    let mut i = 32u32;
    while i > 0 {
        i -= 1;
        if i < s && ((position >> i) & 1) != 0 {
            z = gl64::mul(z, root);
        }
        root = gl64::mul(root, root);
    }
    z
}

/// `f[i]` at position `I`, for `i < count`.
pub fn gl64_factors(log_n: u32, position: u64, count: usize, f: &mut [u64]) {
    if count == 0 {
        return;
    }
    f[0] = gl64_point(log_n, position);
    for i in 1..count {
        f[i] = gl64::mul(f[i - 1], f[i - 1]);
    }
}

/// The fast transform's table for a code of length `2^log_n` and `layers` layers
/// (`gl64_table`). The C++ caches it under a mutex; the port builds it explicitly, so the core has
/// no file-scope mutable state.
pub fn gl64_table(log_n: u32, layers: u32) -> Vec<u64> {
    let n = 1usize << log_n;
    let s = gl64_subgroup_log(log_n);
    let mut tw = vec![0u64; n];
    if layers == 0 {
        return tw;
    }
    {
        let (_, z_part) = tw.split_at_mut(n / 2);
        let z = z_part;
        z[0] = GL64_GENERATOR;
        for b in 0..log_n.saturating_sub(1) {
            let i = b + 1;
            let step = if i < s {
                gl64_pow(GL64_ROOT_32, 1u64 << (31 - i))
            } else {
                gl64_pow(GL64_GENERATOR, 1u64 << (i - s))
            };
            let half = 1usize << b;
            for m in 0..half {
                z[m + half] = gl64::mul(z[m], step);
            }
        }
    }
    for l in 1..layers {
        let at = n >> (l + 1);
        for h in 0..at {
            tw[at + h] = gl64::mul(tw[2 * at + 2 * h], tw[2 * at + 2 * h]);
        }
    }
    tw
}
