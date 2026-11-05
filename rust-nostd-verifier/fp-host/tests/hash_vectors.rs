//! Lane B parity: the verifier's own H/TH, BLAKE2b's F, and every line of
//! `blocks/hash/tests/mode_vectors.txt`.
//!
//! The vector files are the repository's own; `fixtures/earlier_hash_f_vectors.txt` is produced by
//! `verifier/tests/known_answers/blake2b_f.py`.

use fp_core::hash::calls::HashCalls;
use fp_core::hash::domains::{domain_is_leaf, domain_is_vertex, Domain};
use fp_core::hash::earlier::{earlier_hash_f, earlier_hash_h_state, DW, SW};
use fp_core::hash::th::{self, THPW};
use fp_core::hash::modes::{
    chain_absorb, chain_call, chain_call_cells, leaf_bytes, work_test, Digest, Hasher, Tag,
};
use fp_core::hash::blake2b;

const H_VECTORS: &str = include_str!("../../../verifier/tests/hash_vectors.txt");
const MODE_VECTORS: &str = include_str!("../../../blocks/hash/tests/mode_vectors.txt");
const F_VECTORS: &str = include_str!("../../fixtures/earlier_hash_f_vectors.txt");

fn hex_to_u64s(s: &str) -> Vec<u64> {
    assert_eq!(s.len() % 16, 0, "hex length");
    (0..s.len() / 16)
        .map(|i| u64::from_str_radix(&s[16 * i..16 * i + 16], 16).unwrap())
        .collect()
}

fn hex_to_bytes(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0, "hex length");
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
        .collect()
}

fn u32s_hex(words: &[u32]) -> String {
    words.iter().map(|w| format!("{:08x}", w)).collect()
}

fn digest_hex(d: &Digest) -> String {
    d.to_bytes().iter().map(|b| format!("{:02x}", b)).collect()
}

/// `list_bytes()` of the vector generator: word k is ((k + 1) * 0x89ABCDEF) mod 2^32.
fn made(n: usize) -> Vec<u32> {
    (0..n)
        .map(|k| ((k as u32 + 1).wrapping_mul(0x89AB_CDEF)))
        .collect()
}

#[test]
fn earlier_hash_f_matches_python() {
    let mut lines = 0usize;
    for (lineno, line) in F_VECTORS.lines().enumerate() {
        let t: Vec<&str> = line.split_whitespace().collect();
        assert_eq!(t.len(), 6, "line {}", lineno + 1);
        assert_eq!(t[4], "->", "line {}", lineno + 1);
        let h = hex_to_u64s(t[0]);
        let m = hex_to_u64s(t[1]);
        assert_eq!(h.len(), 8);
        assert_eq!(m.len(), 16);
        let tt = u128::from_str_radix(t[2], 16).unwrap();
        let last = match t[3] {
            "0" => false,
            "1" => true,
            _ => panic!("bad last flag at line {}", lineno + 1),
        };
        let want = hex_to_u64s(t[5]);
        assert_eq!(want.len(), 8);
        let mut hh = [0u64; 8];
        hh.copy_from_slice(&h);
        let mut mm = [0u64; 16];
        mm.copy_from_slice(&m);
        let mut calls = HashCalls::new();
        earlier_hash_f(&mut hh, &mm, tt as u64, (tt >> 64) as u64, last, &mut calls);
        assert_eq!(hh.to_vec(), want, "line {}", lineno + 1);
        assert_eq!(calls.f2b, 1, "line {}", lineno + 1);
        lines += 1;
    }
    assert_eq!(lines, 200);
}

#[test]
fn earlier_hash_and_th_match_the_repository_vectors() {
    let mut h_lines = 0usize;
    let mut th_lines = 0usize;
    for (lineno, line) in H_VECTORS.lines().enumerate() {
        let t: Vec<&str> = line.split_whitespace().collect();
        match t[0] {
            "H" => {
                let num: u32 = t[1].parse().unwrap();
                let n: usize = t[2].parse().unwrap();
                let w = made(n);
                let mut out = [0u32; SW];
                let mut calls = HashCalls::new();
                earlier_hash_h_state(&mut out, num, &w, n as u64, 1, &mut calls);
                assert_eq!(u32s_hex(&out), t[3], "H line {}", lineno + 1);
                h_lines += 1;
            }
            "TH" => {
                let n: usize = t[1].parse().unwrap();
                let w = made(n);
                let mut out = [0u32; DW];
                let mut calls = HashCalls::new();
                th::th(&mut out, &w, &mut calls);
                assert_eq!(u32s_hex(&out), t[2], "TH line {}", lineno + 1);
                th_lines += 1;
            }
            other => panic!("unknown vector kind {} at line {}", other, lineno + 1),
        }
    }
    assert_eq!((h_lines, th_lines), (44, 13));
    assert_eq!(THPW, 128);
}

#[test]
fn mode_vectors_match_the_repository_vectors() {
    let mut lines = 0usize;
    for (lineno, line) in MODE_VECTORS.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let t: Vec<&str> = line.split_whitespace().collect();
        assert_eq!(t.len(), 9, "line {}", lineno + 1);
        let number: u32 = t[0].parse().unwrap();
        let tree: u64 = t[1].parse().unwrap();
        let index: u64 = t[2].parse().unwrap();
        let width: u64 = t[4].parse().unwrap();
        let salt_bytes: u64 = t[5].parse().unwrap();
        let n: usize = t[6].parse().unwrap();
        let length: usize = t[7].parse().unwrap();
        let want = t[8];
        let start = if t[3] == "-" {
            Digest::zero()
        } else {
            let start_bytes = hex_to_bytes(t[3]);
            assert_eq!(start_bytes.len(), 32, "line {}", lineno + 1);
            Digest::from_bytes(start_bytes.as_slice().try_into().unwrap())
        };
        let mut data = vec![0u8; n];
        for (i, x) in data.iter_mut().enumerate() {
            *x = ((7 * i + 3) % 251) as u8;
        }
        if salt_bytes != 0 {
            let salt_at = n - salt_bytes as usize;
            for i in (8 * width as usize)..n {
                data[i] = if i < salt_at {
                    0
                } else {
                    ((5 * (i - salt_at) + 1) % 251) as u8
                };
            }
        }
        let domain = Domain::from_word(number);
        let mut calls = HashCalls::new();
        if domain == Domain::ChainQuery {
            assert_eq!(length, 64, "line {}", lineno + 1);
            let mut h = chain_absorb(&start, index, tree, &mut calls);
            h.push(&data[..n - 16]);
            let word = u64::from_le_bytes(data[n - 16..n - 8].try_into().unwrap());
            let nonce = u64::from_le_bytes(data[n - 8..].try_into().unwrap());
            h.push_u64(word & 0xFFFF);
            let prefix = h.before_nonce();
            let call = chain_call(&prefix, nonce, word >> 16, &mut calls);
            let mut bytes = [0u8; 64];
            for i in 0..64 {
                bytes[i] = (call.w[i / 8] >> (8 * (i % 8))) as u8;
            }
            let got: String = bytes.iter().map(|b| format!("{:02x}", b)).collect();
            assert_eq!(got, want, "line {}", lineno + 1);
        } else {
            assert_eq!(length, 32, "line {}", lineno + 1);
            let tag = if domain_is_leaf(domain) {
                Tag::leaf(domain, tree as u32, &start, width, salt_bytes)
            } else if domain_is_vertex(domain) {
                Tag::vertex(domain, tree as u32, &start)
            } else {
                Tag::plain(domain, tree)
            };
            let mut h = if domain == Domain::TestCoins {
                Hasher::new_with_start(&tag, index, &start, &mut calls)
            } else {
                Hasher::new(&tag, index, &mut calls)
            };
            if domain_is_leaf(domain) {
                assert_eq!(
                    data.len() as u64,
                    leaf_bytes(width, salt_bytes) - 16,
                    "leaf length at line {}",
                    lineno + 1
                );
            }
            h.push(&data);
            let d = h.finish();
            assert_eq!(digest_hex(&d), want, "line {}", lineno + 1);
        }
        lines += 1;
    }
    assert_eq!(lines, 58);
}

#[test]
fn rfc7693_appendix_a_abc() {
    // BLAKE2b-512 of "abc", RFC 7693 Appendix A.
    let abc = b"abc";
    let mut h = [0u64; 8];
    blake2b::begin64(&mut h, &blake2b::Start::default(), 64);
    let blocks = if abc.is_empty() {
        1
    } else {
        (abc.len() + 127) / 128
    };
    for k in 0..blocks {
        let mut m = [0u64; 16];
        let have = std::cmp::min(128, abc.len().saturating_sub(128 * k));
        for i in 0..have {
            m[i / 8] |= (abc[128 * k + i] as u64) << (8 * (i % 8));
        }
        blake2b::f(&mut h, &m, (128 * k + have) as u64, 0, k + 1 == blocks);
    }
    let mut out = [0u8; 64];
    for i in 0..64 {
        out[i] = (h[i / 8] >> (8 * (i % 8))) as u8;
    }
    let got: String = out.iter().map(|b| format!("{:02x}", b)).collect();
    assert_eq!(
        got,
        "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1\
         7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"
    );
}

fn cells_case<const CELLS: usize>() {
    let rho = Digest { w: [1, 2, 3, 4, 5, 6, 7, 8] };
    let mut cells = [0u64; CELLS];
    let mut x = 0x1234_5678_9abc_def0u64;
    for c in &mut cells {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *c = x;
    }
    cells[CELLS - 1] &= 0xFFFF;
    let round = 42u64;
    let chain = 77u64;
    let nonce = 0xdead_beef_1234_5678u64;
    for j in [0u64, 1, 77, (1u64 << 48) - 1] {
        let mut calls = HashCalls::new();
        let prefix = {
            let mut h = chain_absorb(&rho, round, chain, &mut calls);
            for c in &cells[..CELLS - 1] {
                h.push_u64(*c);
            }
            h.push_u64(cells[CELLS - 1]);
            h.before_nonce()
        };
        let a = chain_call(&prefix, nonce, j, &mut calls);
        let b = chain_call_cells(&rho, round, &cells, nonce, j, chain, &mut calls);
        assert_eq!(a, b, "CELLS {} j {}", CELLS, j);
    }
}

#[test]
fn chain_call_cells_matches_chain_call() {
    cells_case::<1>();
    cells_case::<2>();
    cells_case::<7>();
    cells_case::<14>();
    cells_case::<15>();
    cells_case::<16>();
    cells_case::<17>();
    cells_case::<33>();
}

#[test]
fn work_test_matches_the_cpp_cases() {
    assert!(work_test(u64::MAX, 0));
    assert!(work_test(0, 64));
    assert!(!work_test(1, 1));
    assert!(work_test(2, 1));
    assert!(!work_test(1u64 << 63, 64));
    assert!(work_test(1u64 << 63, 63));
    assert!(work_test(0xFF00, 8));
    assert!(!work_test(0xFF00, 9));
}
