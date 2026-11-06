//! `TH`, the tree hash over the verifier's own hash H, ported from `verifier/src/vf_common.h`
//! (`thLevel()` and `TH()`).
//!
//! One level hashes chunks of `THPW` words under the domain number 10; later levels use 11, until
//! one digest is left. `parFor` is serial here, as it is with the default `-j`.

use alloc::vec;
use alloc::vec::Vec;

use super::calls::HashCalls;
use super::earlier::{earlier_hash_h_digest, DW};

/// `THPW = 16 * DW`.
pub const THPW: usize = 16 * DW;

/// One level of `TH` (`thLevel`).
fn th_level(num: u32, w: &[u32], calls: &mut HashCalls) -> Vec<u32> {
    let n = w.len();
    let nc = (n + THPW - 1) / THPW;
    let blk = 1usize << 12;
    let mut nx = vec![0u32; DW * nc];
    let groups = (nc + blk - 1) / blk;
    // The serial branch of parFor: for each block of chunks, hash each chunk.
    for b in 0..groups {
        let end = if nc < (b + 1) * blk { nc } else { (b + 1) * blk };
        for i in b * blk..end {
            let take = if n - THPW * i < THPW {
                n - THPW * i
            } else {
                THPW
            };
            let mut d = [0u32; DW];
            earlier_hash_h_digest(
                &mut d,
                num,
                &w[THPW * i..THPW * i + take],
                take as u64,
                1,
                calls,
            );
            nx[DW * i..DW * i + DW].copy_from_slice(&d);
        }
    }
    nx
}

/// `TH`: the digest of a list of at least DW words (`TH`).
pub fn th(out: &mut [u32; DW], w: &[u32], calls: &mut HashCalls) {
    assert!(w.len() >= DW, "internal-th");
    let mut cur = th_level(10, w, calls);
    while cur.len() > DW {
        let nx = th_level(11, &cur, calls);
        cur = nx;
    }
    assert!(cur.len() == DW, "internal-th");
    out.copy_from_slice(&cur);
}

/// The same that allocates its output.
pub fn th_vec(w: &[u32], calls: &mut HashCalls) -> Vec<u32> {
    let mut out = [0u32; DW];
    th(&mut out, w, calls);
    out.to_vec()
}
