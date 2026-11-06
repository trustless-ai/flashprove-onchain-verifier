//! Lane B counters: the same input sequence as `scripts/cpp_vectors/hash_counters.cpp` must give
//! the same `HashCalls::f2b` and `HashCalls::blk`. The C++ numbers are in
//! `fixtures/hash_counts.txt`, produced with `BLK_COUNT_HASH_CALLS=1`.

use fp_core::hash::calls::HashCalls;
use fp_core::hash::domains::Domain;
use fp_core::hash::earlier::earlier_hash_h_digest;
use fp_core::hash::modes::Hasher;
use fp_core::hash::th;

const COUNTS: &str = include_str!("../../fixtures/hash_counts.txt");

fn made(n: usize) -> Vec<u32> {
    (0..n)
        .map(|k| (k as u32 + 1).wrapping_mul(0x89AB_CDEF))
        .collect()
}

fn data(n: usize) -> Vec<u8> {
    (0..n).map(|i| (7 * i + 3) as u8).collect()
}

fn run(group: &str) -> HashCalls {
    let mut calls = HashCalls::new();
    match group {
        "H" => {
            for n in [0usize, 1, 7, 8, 127, 128, 129, 1000] {
                let w = made(n);
                for num in [3u32, 10, 107] {
                    let mut d = [0u32; 8];
                    earlier_hash_h_digest(&mut d, num, &w, n as u64, 1, &mut calls);
                }
            }
        }
        "TH" => {
            for n in [8usize, 127, 128, 129, 1000] {
                let w = made(n);
                let mut d = [0u32; 8];
                th::th(&mut d, &w, &mut calls);
            }
        }
        "BLOCKS" => {
            for n in [0usize, 1, 127, 128, 129, 1000] {
                let d = data(n);
                let tag = fp_core::hash::modes::Tag::plain(Domain::Statement, 0);
                let mut h = Hasher::new(&tag, 1, &mut calls);
                h.push(&d);
                h.finish();
            }
        }
        "MIXED" => {
            let w = made(129);
            let mut d = [0u32; 8];
            earlier_hash_h_digest(&mut d, 10, &w, 129, 1, &mut calls);
            let bytes = data(129);
            let tag = fp_core::hash::modes::Tag::plain(Domain::Statement, 0);
            let mut h = Hasher::new(&tag, 1, &mut calls);
            h.push(&bytes);
            h.finish();
        }
        other => panic!("unknown counter group {}", other),
    }
    calls
}

#[test]
fn counters_match_the_cpp_reference() {
    let mut seen = 0usize;
    for line in COUNTS.lines() {
        let t: Vec<&str> = line.split_whitespace().collect();
        assert_eq!(t[0], "COUNTS");
        let f2b: u64 = t[2].parse().unwrap();
        let blk: u64 = t[3].parse().unwrap();
        let got = run(t[1]);
        assert_eq!(got.f2b, f2b, "{} f2b", t[1]);
        assert_eq!(got.blk, blk, "{} blk", t[1]);
        assert_eq!(got.total(), f2b + blk, "{} total", t[1]);
        seen += 1;
    }
    assert_eq!(seen, 4);
}
