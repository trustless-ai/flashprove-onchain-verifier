//! Candidate B: a hand-written BLAKE2b compression: the twelve rounds unrolled, the SIGMA indices
//! constant, `G` always inline, and the rotations written as explicit shifts (the RV64IM target has
//! no rotate instruction). `f_rot` is the same code with `rotate_right`, to check that rustc/LLVM
//! lowers the two forms identically on this target.

const IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

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

#[inline(always)]
fn g_rot(v: &mut [u64; 16], x: u64, y: u64, a: usize, b: usize, c: usize, d: usize) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

/// Explicit shifts instead of `rotate_right`: `rotr(x, n) = (x >> n) | (x << (64 - n))`.
#[inline(always)]
fn g_shifts(v: &mut [u64; 16], x: u64, y: u64, a: usize, b: usize, c: usize, d: usize) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = ((v[d] ^ v[a]) >> 32) | ((v[d] ^ v[a]) << 32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = ((v[b] ^ v[c]) >> 24) | ((v[b] ^ v[c]) << 40);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = ((v[d] ^ v[a]) >> 16) | ((v[d] ^ v[a]) << 48);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = ((v[b] ^ v[c]) >> 63) | ((v[b] ^ v[c]) << 1);
}

macro_rules! rounds {
    ($g:ident, $v:expr, $m:expr, $r:expr) => {{
        $g($v, $m[SIGMA[$r][0]], $m[SIGMA[$r][1]], 0, 4, 8, 12);
        $g($v, $m[SIGMA[$r][2]], $m[SIGMA[$r][3]], 1, 5, 9, 13);
        $g($v, $m[SIGMA[$r][4]], $m[SIGMA[$r][5]], 2, 6, 10, 14);
        $g($v, $m[SIGMA[$r][6]], $m[SIGMA[$r][7]], 3, 7, 11, 15);
        $g($v, $m[SIGMA[$r][8]], $m[SIGMA[$r][9]], 0, 5, 10, 15);
        $g($v, $m[SIGMA[$r][10]], $m[SIGMA[$r][11]], 1, 6, 11, 12);
        $g($v, $m[SIGMA[$r][12]], $m[SIGMA[$r][13]], 2, 7, 8, 13);
        $g($v, $m[SIGMA[$r][14]], $m[SIGMA[$r][15]], 3, 4, 9, 14);
    }};
}

#[inline]
fn start(h: &[u64; 8], t_low: u64, t_high: u64, last: bool) -> [u64; 16] {
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
    v
}

/// The unrolled compression with `rotate_right` (identical codegen to Candidate A's `f`, but
/// without the round loop and with constant SIGMA indices).
pub fn f_rot(h: &mut [u64; 8], m: &[u64; 16], t_low: u64, t_high: u64, last: bool) {
    let mut v = start(h, t_low, t_high, last);
    rounds!(g_rot, &mut v, m, 0);
    rounds!(g_rot, &mut v, m, 1);
    rounds!(g_rot, &mut v, m, 2);
    rounds!(g_rot, &mut v, m, 3);
    rounds!(g_rot, &mut v, m, 4);
    rounds!(g_rot, &mut v, m, 5);
    rounds!(g_rot, &mut v, m, 6);
    rounds!(g_rot, &mut v, m, 7);
    rounds!(g_rot, &mut v, m, 8);
    rounds!(g_rot, &mut v, m, 9);
    rounds!(g_rot, &mut v, m, 10);
    rounds!(g_rot, &mut v, m, 11);
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

/// The unrolled compression with explicit shifts.
pub fn f_shifts(h: &mut [u64; 8], m: &[u64; 16], t_low: u64, t_high: u64, last: bool) {
    let mut v = start(h, t_low, t_high, last);
    rounds!(g_shifts, &mut v, m, 0);
    rounds!(g_shifts, &mut v, m, 1);
    rounds!(g_shifts, &mut v, m, 2);
    rounds!(g_shifts, &mut v, m, 3);
    rounds!(g_shifts, &mut v, m, 4);
    rounds!(g_shifts, &mut v, m, 5);
    rounds!(g_shifts, &mut v, m, 6);
    rounds!(g_shifts, &mut v, m, 7);
    rounds!(g_shifts, &mut v, m, 8);
    rounds!(g_shifts, &mut v, m, 9);
    rounds!(g_shifts, &mut v, m, 10);
    rounds!(g_shifts, &mut v, m, 11);
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}
