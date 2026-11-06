//! BLAKE2b's compression function and first chaining values, ported from
//! `blocks/hash/blake2b_f.h`.
//!
//! The compression is RFC 7693, section 3.2, with 64-bit words and twelve rounds. `F` is the bare
//! compression; `compress64` adds the format's `Tweak` and counts the call.

use super::calls::HashCalls;
use super::tweak::Tweak;

pub const CVW: usize = 16;
pub const BLKW: usize = 32;

/// `blake2b_IV` (RFC 7693, section 2.6).
pub const IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

/// `blake2b_sigma` (RFC 7693, section 2.7).
const SIGMA: [[usize; 16]; 12] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
];

/// The BLAKE2b start: salt and personalization as eight 32-bit words (`Blake2bF::Start`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Start {
    pub w: [u32; 8],
}

/// BLAKE2b's `G` (RFC 7693, section 3.1), with the sums modulo 2^64. The unrolled compression
/// passes the round's two message words and the four state indices; all of its array indices are
/// then compile-time constants.
#[inline(always)]
fn g(v: &mut [u64; 16], x: u64, y: u64, a: usize, b: usize, c: usize, d: usize) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

/// One round's eight `G` calls (`SIGMA[r]`, unrolled).  a runtime round loop with
/// `m[SIGMA[r][..]]` cost 2,955 cycles per compression on the zkVM target; this unrolled form
/// costs 2,261 (measured in `zkvm/bench`, same public values).
macro_rules! rounds {
    ($v:expr, $m:expr, $r:expr) => {{
        g($v, $m[SIGMA[$r][0]], $m[SIGMA[$r][1]], 0, 4, 8, 12);
        g($v, $m[SIGMA[$r][2]], $m[SIGMA[$r][3]], 1, 5, 9, 13);
        g($v, $m[SIGMA[$r][4]], $m[SIGMA[$r][5]], 2, 6, 10, 14);
        g($v, $m[SIGMA[$r][6]], $m[SIGMA[$r][7]], 3, 7, 11, 15);
        g($v, $m[SIGMA[$r][8]], $m[SIGMA[$r][9]], 0, 5, 10, 15);
        g($v, $m[SIGMA[$r][10]], $m[SIGMA[$r][11]], 1, 6, 11, 12);
        g($v, $m[SIGMA[$r][12]], $m[SIGMA[$r][13]], 2, 7, 8, 13);
        g($v, $m[SIGMA[$r][14]], $m[SIGMA[$r][15]], 3, 4, 9, 14);
    }};
}

/// `F(h, m, t_low, t_high, last)`: one BLAKE2b compression, counted by the caller if required.
#[inline]
pub fn f(h: &mut [u64; 8], m: &[u64; 16], t_low: u64, t_high: u64, last: bool) {
    let mut v = [0u64; 16];
    v[..8].copy_from_slice(h);
    v[8] = IV[0];
    v[9] = IV[1];
    v[10] = IV[2];
    v[11] = IV[3];
    v[12] = IV[4] ^ t_low;
    v[13] = IV[5] ^ t_high;
    v[14] = IV[6] ^ if last { u64::MAX } else { 0 };
    v[15] = IV[7];
    rounds!(&mut v, m, 0);
    rounds!(&mut v, m, 1);
    rounds!(&mut v, m, 2);
    rounds!(&mut v, m, 3);
    rounds!(&mut v, m, 4);
    rounds!(&mut v, m, 5);
    rounds!(&mut v, m, 6);
    rounds!(&mut v, m, 7);
    rounds!(&mut v, m, 8);
    rounds!(&mut v, m, 9);
    rounds!(&mut v, m, 10);
    rounds!(&mut v, m, 11);
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

/// `Blake2bF::compress64`: `F` with the tweak's counter words, counted in `HashCalls::blk`.
#[inline]
pub fn compress64(h: &mut [u64; 8], m: &[u64; 16], t: &Tweak, calls: &mut HashCalls) {
    calls.blk += 1;
    f(
        h,
        m,
        t.c0 as u64 | (t.c1 as u64) << 32,
        t.num as u64 | (t.l as u64) << 32,
        t.last,
    );
}

/// `Blake2bF::compress`: `compress64` on words of 32 bits, two making one word of F.
#[inline]
pub fn compress(cv: &mut [u32; CVW], block: &[u32; BLKW], t: &Tweak, calls: &mut HashCalls) {
    let mut h = [0u64; 8];
    for i in 0..8 {
        h[i] = cv[2 * i] as u64 | (cv[2 * i + 1] as u64) << 32;
    }
    let mut m = [0u64; 16];
    for i in 0..16 {
        m[i] = block[2 * i] as u64 | (block[2 * i + 1] as u64) << 32;
    }
    compress64(&mut h, &m, t, calls);
    for i in 0..8 {
        cv[2 * i] = h[i] as u32;
        cv[2 * i + 1] = (h[i] >> 32) as u32;
    }
}

/// The first word of BLAKE2b's parameter block (`Blake2bF::param_word0`).
#[inline]
pub const fn param_word0(digest_bytes: u32) -> u64 {
    (digest_bytes as u64) | (1u64 << 16) | (1u64 << 24)
}

/// The first chaining value with salt and personalization (`Blake2bF::begin64`).
#[inline]
pub fn begin64(h: &mut [u64; 8], start: &Start, digest_bytes: u32) {
    h[0] = IV[0] ^ param_word0(digest_bytes);
    h[1] = IV[1];
    h[2] = IV[2];
    h[3] = IV[3];
    h[4] = IV[4] ^ (start.w[0] as u64 | (start.w[1] as u64) << 32);
    h[5] = IV[5] ^ (start.w[2] as u64 | (start.w[3] as u64) << 32);
    h[6] = IV[6] ^ (start.w[4] as u64 | (start.w[5] as u64) << 32);
    h[7] = IV[7] ^ (start.w[6] as u64 | (start.w[7] as u64) << 32);
}

/// The same on 32-bit words (`Blake2bF::begin`).
#[inline]
pub fn begin(cv: &mut [u32; CVW], start: &Start, digest_bytes: u32) {
    let mut h = [0u64; 8];
    begin64(&mut h, start, digest_bytes);
    for i in 0..8 {
        cv[2 * i] = h[i] as u32;
        cv[2 * i + 1] = (h[i] >> 32) as u32;
    }
}

/// The counter of block `s`, which is not the last (`Blake2bF::step`).
#[inline]
pub fn step(s: u32) -> Tweak {
    Tweak {
        c0: 4 * BLKW as u32 * s.wrapping_add(1),
        c1: 0,
        l: 0,
        num: 0,
        last: false,
    }
}

/// The counter of the last block, whose length is `bytes` (`Blake2bF::last`).
#[inline]
pub fn last(bytes: u32) -> Tweak {
    Tweak {
        c0: bytes,
        c1: 0,
        l: 0,
        num: 0,
        last: true,
    }
}

/// The first chaining value of BLAKE2b-512 (`Blake2bF::first64`).
#[inline]
pub fn first64(h: &mut [u64; 8]) {
    h[0] = IV[0] ^ param_word0(64);
    h[1] = IV[1];
    h[2] = IV[2];
    h[3] = IV[3];
    h[4] = IV[4];
    h[5] = IV[5];
    h[6] = IV[6];
    h[7] = IV[7];
}

/// The same on 32-bit words (`Blake2bF::first`).
#[inline]
pub fn first(cv: &mut [u32; CVW]) {
    let mut h = [0u64; 8];
    first64(&mut h);
    for i in 0..8 {
        cv[2 * i] = h[i] as u32;
        cv[2 * i + 1] = (h[i] >> 32) as u32;
    }
}
