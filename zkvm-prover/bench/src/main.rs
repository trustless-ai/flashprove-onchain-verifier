//! The microbenchmark guest: `n` BLAKE2b compressions of one 128-byte block in one of four
//! implementations.
//!
//!   mode 0: fp-core's current `blake2b::f` (the verifier's implementation)
//!   mode 1: the hand-written unrolled compression with explicit shifts (Candidate B)
//!   mode 2: `blake2b_simd` 1.0.5, no_std, portable path, a one-block hash (Candidate C)
//!   mode 3: the same unrolled compression but with `rotate_right` (Candidate B')
//!
//! Input: mode (u32), n (u64). Public output: the sink, the chaining value and n.

#![no_std]
#![no_main]

extern crate alloc;

mod fast;

use sp1_zkvm::io;

sp1_zkvm::entrypoint!(main);

pub fn main() {
    let mode = io::read::<u32>();
    let n = io::read::<u64>();
    let mut h = fp_core::hash::blake2b::IV;
    let mut m = [0u64; 16];
    let mut i = 0;
    while i < 16 {
        m[i] = 0x0123_4567_89ab_cdefu64.wrapping_mul(i as u64 + 1);
        i += 1;
    }
    let mut sink = 0u64;
    match mode {
        0 => {
            let mut j = 0;
            while j < n {
                fp_core::hash::blake2b::f(&mut h, &m, 0, 0, true);
                sink ^= h[0];
                j += 1;
            }
        }
        1 => {
            let mut j = 0;
            while j < n {
                fast::f_shifts(&mut h, &m, 0, 0, true);
                sink ^= h[0];
                j += 1;
            }
        }
        2 => {
            let mut block = [0x5au8; 128];
            let mut j = 0;
            while j < n {
                // Vary one byte so that the hash of a constant block cannot be hoisted.
                block[0] = j as u8;
                let out = blake2b_simd::Params::new().hash(&block);
                let b = out.as_bytes();
                sink ^= u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]);
                j += 1;
            }
        }
        3 => {
            let mut j = 0;
            while j < n {
                fast::f_rot(&mut h, &m, 0, 0, true);
                sink ^= h[0];
                j += 1;
            }
        }
        _ => {}
    }
    io::commit(&sink);
    io::commit(&h);
    io::commit(&n);
}
