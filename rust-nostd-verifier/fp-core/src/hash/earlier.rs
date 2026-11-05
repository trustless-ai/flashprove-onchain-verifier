//! The verifier's own hash `H(num; w)`, ported from `verifier/src/vf_earlier_hash_f.h` and
//! `verifier/src/vf_earlier_hash.h`.
//!
//! F is BLAKE2b's compression function; `H` feeds it with a domain-separation number `num` and a
//! length `l` in the high half of the counter. The call count is `HashCalls::f2b`, as C++'s
//! `f2b::calls_of_this_thread` is for the verifier's hash.

use alloc::vec::Vec;

use super::blake2b;
use super::calls::HashCalls;

/// `SW`: the state, in 32-bit words (`vf_widths_and_bounds.h`).
pub const SW: usize = 16;
/// `BLKW`: one input block, in 32-bit words.
pub const BLKW: usize = 32;
/// `DW`: a digest, in 32-bit words.
pub const DW: usize = 8;

/// Two 32-bit words make a 64-bit word of F, the low word first (`words64`).
pub fn words64(out: &mut [u64], w: &[u32], n64: usize) {
    for i in 0..n64 {
        out[i] = w[2 * i] as u64 | (w[2 * i + 1] as u64) << 32;
    }
}

/// The inverse of `words64` (`words32`).
pub fn words32(out: &mut [u32], x: &[u64], n64: usize) {
    for i in 0..n64 {
        out[2 * i] = x[i] as u32;
        out[2 * i + 1] = (x[i] >> 32) as u32;
    }
}

/// `cv := F(cv, m, t, last)`, counted in `HashCalls::f2b` (`earlier_hash_c`).
///
/// Low 64 bits of t: `c0 + 2^32 c1`. High 64 bits: `num + 2^32 l`.
pub fn earlier_hash_c(
    cv: &mut [u32; SW],
    m: &[u32; BLKW],
    c0: u32,
    c1: u32,
    l: u32,
    num: u32,
    last: bool,
    calls: &mut HashCalls,
) {
    let mut h = [0u64; SW / 2];
    let mut b = [0u64; BLKW / 2];
    words64(&mut h, cv, SW / 2);
    words64(&mut b, m, BLKW / 2);
    earlier_hash_f(
        &mut h,
        &b,
        c0 as u64 | (c1 as u64) << 32,
        num as u64 | (l as u64) << 32,
        last,
        calls,
    );
    words32(cv, &h, SW / 2);
}

/// `f2b::F`: BLAKE2b's compression on 64-bit words, counted in `HashCalls::f2b`.
pub fn earlier_hash_f(
    h: &mut [u64; 8],
    m: &[u64; 16],
    t_low: u64,
    t_high: u64,
    last: bool,
    calls: &mut HashCalls,
) {
    calls.f2b += 1;
    blake2b::f(h, m, t_low, t_high, last);
}

/// The initial state: BLAKE2b-512's (`earlier_hash_initial_state`).
pub fn earlier_hash_initial_state(cv: &mut [u32; SW]) {
    let mut h = [0u64; SW / 2];
    h.copy_from_slice(&blake2b::IV[..8]);
    h[0] ^= 0x0101_0040;
    words32(cv, &h, SW / 2);
}

/// `H`'s state with any `l` (`earlier_hash_h_state_with_length`).
///
/// The L words `w[0], w[stride], ...` are hashed in blocks of BLKW words: at least one, the last
/// padded with zeros. `x` is added to `c1`; no caller of the verifier passes a nonzero `x`.
#[allow(clippy::too_many_arguments)]
pub fn earlier_hash_h_state_with_length(
    out: &mut [u32; SW],
    num: u32,
    l: u32,
    w: &[u32],
    big_l: u64,
    stride: u64,
    x: u32,
    calls: &mut HashCalls,
) {
    earlier_hash_initial_state(out);
    let mut nb = (big_l + BLKW as u64 - 1) / BLKW as u64;
    if nb == 0 {
        nb = 1;
    }
    for b in 0..nb {
        let mut m = [0u32; BLKW];
        for i in 0..BLKW {
            let j = b * BLKW as u64 + i as u64;
            m[i] = if j < big_l {
                w[(j * stride) as usize]
            } else {
                0
            };
        }
        let last = b + 1 == nb;
        let fed = if last {
            4 * big_l
        } else {
            4 * BLKW as u64 * (b + 1)
        };
        earlier_hash_c(
            out,
            &m,
            fed as u32,
            ((fed >> 32) as u32).wrapping_add(x),
            l,
            num,
            last,
            calls,
        );
    }
}

/// The state of `H(num; w)`, with `l = L` (`earlier_hash_h_state`).
pub fn earlier_hash_h_state(
    out: &mut [u32; SW],
    num: u32,
    w: &[u32],
    big_l: u64,
    stride: u64,
    calls: &mut HashCalls,
) {
    earlier_hash_h_state_with_length(out, num, big_l as u32, w, big_l, stride, 0, calls);
}

/// The digest of `H(num; w)`: the first DW words of the state (`earlier_hash_h_digest`).
pub fn earlier_hash_h_digest(
    out: &mut [u32; DW],
    num: u32,
    w: &[u32],
    big_l: u64,
    stride: u64,
    calls: &mut HashCalls,
) {
    let mut s = [0u32; SW];
    earlier_hash_h_state(&mut s, num, w, big_l, stride, calls);
    out.copy_from_slice(&s[..DW]);
}

/// A convenience wrapper that returns the DW-word digest and owns its state buffer.
pub fn earlier_hash_h_digest_vec(
    num: u32,
    w: &[u32],
    big_l: u64,
    stride: u64,
    calls: &mut HashCalls,
) -> Vec<u32> {
    let mut out = [0u32; DW];
    earlier_hash_h_digest(&mut out, num, w, big_l, stride, calls);
    out.to_vec()
}
