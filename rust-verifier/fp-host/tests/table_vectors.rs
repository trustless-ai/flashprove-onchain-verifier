//! Replay of `scripts/cpp_vectors/table_vectors.cpp`: the four public tables, their digests, the
//! parameter file's 32 digest words, and the gate's rejection names for four mutated digests.
//!
//! The fixture `fixtures/table_vectors.txt` is the tool's output, byte for byte. Its format is
//! documented at the top of the tool.

use fp_core::frame::parameters::{read_parameters, Parameters};
use fp_core::hash::calls::HashCalls;
use fp_core::hash::earlier::DW;
use fp_core::verifier::tables::{
    check_table_digests, exp_table, rope_table, sigmoid_table, silu_table, table_digest, TableFacts,
    TableParams, TBLW,
};

const VECTORS: &str = include_str!("../../fixtures/table_vectors.txt");
const POLICY: &[u8] = include_bytes!("../../fixtures/config/policy.txt");

/// The four tables in the tool's order.
const TABLES: [&str; 4] = ["silu", "sigmoid", "rope", "exp"];

fn words8(s: &str) -> [u32; DW] {
    let v: Vec<u32> = s.split(' ').map(|w| u32::from_str_radix(w, 16).unwrap()).collect();
    assert_eq!(v.len(), DW, "digest {}", s);
    let mut out = [0u32; DW];
    out.copy_from_slice(&v);
    out
}

/// The parameter file's lines `tsilu0` .. `texp7`, parsed strictly.
fn policy_digest_words(rest: &[u8]) -> [[u32; DW]; 4] {
    let mut out = [[0u32; DW]; 4];
    let mut seen = [[false; DW]; 4];
    for line in rest.split(|&c| c == b'\n') {
        let text = core::str::from_utf8(line).unwrap();
        for (k, prefix) in ["tsilu", "tsig", "trope", "texp"].iter().enumerate() {
            if let Some(tail) = text.strip_prefix(prefix) {
                let (idx, value) = tail.split_once(' ').expect("a digest line has a value");
                let idx: usize = idx.parse().unwrap();
                assert!(!seen[k][idx], "digest line {}{} is repeated", prefix, idx);
                seen[k][idx] = true;
                out[k][idx] = value.parse().unwrap();
            }
        }
    }
    assert!(seen.iter().flatten().all(|&s| s), "the policy has all 32 digest lines");
    out
}

/// One copy of the parameter file's tail with the value of `name`'s line flipped in its low bit.
fn flip_word(rest: &[u8], name: &str) -> Vec<u8> {
    let text = core::str::from_utf8(rest).unwrap();
    let prefix = format!("{} ", name);
    let mut out = Vec::new();
    for (i, line) in text.split('\n').enumerate() {
        if i > 0 {
            out.push(b'\n');
        }
        if let Some(value) = line.strip_prefix(&prefix) {
            let v: u32 = value.parse().unwrap();
            out.extend_from_slice(format!("{} {}", name, v ^ 1).as_bytes());
        } else {
            out.extend_from_slice(line.as_bytes());
        }
    }
    out
}

#[test]
fn table_vectors_match_the_cpp_reference() {
    let lines: Vec<&str> = VECTORS.lines().collect();
    let mut at = 0usize;

    // PARAMS: the values that the tool read from the parameter file.
    let params_line = lines[at].strip_prefix("PARAMS ").expect("PARAMS");
    at += 1;
    let get = |key: &str| -> u64 {
        params_line
            .split(' ')
            .find_map(|kv| kv.strip_prefix(&format!("{}=", key)))
            .unwrap_or_else(|| panic!("PARAMS has {}", key))
            .parse()
            .unwrap()
    };
    let params = TableParams {
        eg: get("eg") as u32,
        smax: get("smax") as i32,
        gcl: get("gcl") != 0,
        theta0: get("theta0"),
        cs: get("cs") as u32,
        dh: get("dh"),
        lt: get("lt") as u32,
        s: get("s") as u32,
        rx: get("rx") as u32,
    };
    let ne = get("ne");

    // POLICY: the parameter file's 32 digest words.
    let policy_line = lines[at].strip_prefix("POLICY ").expect("POLICY");
    at += 1;
    let policy_words: Vec<[u32; DW]> = {
        let v: Vec<&str> = policy_line.split(' ').collect();
        assert_eq!(v.len(), TBLW);
        v.chunks(DW).map(words8vec).collect()
    };

    // MATCH: every computed digest equals its line on the reference.
    let match_line = lines[at].strip_prefix("MATCH ").expect("MATCH");
    at += 1;
    for t in TABLES {
        assert!(match_line.contains(&format!("{}=1", t)), "MATCH {}: {}", t, match_line);
    }

    // MUTATION: the name that the gate prints for a flipped word.
    let mut mutations = Vec::new();
    for _ in 0..4 {
        let m: Vec<&str> = lines[at].split(' ').collect();
        assert_eq!(m[0], "MUTATION");
        mutations.push((m[1].to_string(), m[2].to_string()));
        at += 1;
    }
    assert_eq!(
        mutations,
        vec![
            ("silu".to_string(), "table-digest-silu".to_string()),
            ("sigmoid".to_string(), "table-digest-sigmoid".to_string()),
            ("rope".to_string(), "table-digest-rope".to_string()),
            ("exp".to_string(), "table-digest-exp".to_string()),
        ]
    );

    // Rebuild all four tables and compare every entry and digest.
    let mut calls = HashCalls::new();
    let built: [Vec<u32>; 4] = {
        let (tt, u0) = exp_table(params.s, params.rx);
        assert_eq!(tt.len() as u64, u0, "the softmax list has u0 entries");
        let exp_words: Vec<u32> = tt[..u0 as usize].iter().map(|&x| x as u32).collect();
        [
            silu_table(&params),
            sigmoid_table(&params, ne > 0).expect("NE > 0 in the fixture"),
            rope_table(params.theta0, params.cs, params.dh, 1u64 << params.lt),
            exp_words,
        ]
    };
    let mut digests = [[0u32; DW]; 4];
    for (k, name) in TABLES.iter().enumerate() {
        let header = lines[at].strip_prefix("TABLE ").expect("TABLE");
        at += 1;
        let h: Vec<&str> = header.split(' ').collect();
        assert_eq!(h[0], *name);
        let count: usize = h[1].parse().unwrap();
        let digest = words8(&h[2..].join(" "));
        assert_eq!(count, built[k].len(), "{} entries", name);
        let mut entries = Vec::with_capacity(count);
        while entries.len() < count {
            for w in lines[at].split(' ') {
                entries.push(u32::from_str_radix(w, 16).unwrap());
            }
            at += 1;
        }
        assert_eq!(entries.len(), count, "{} entries", name);
        assert_eq!(entries, built[k], "{}: every entry", name);
        assert_eq!(table_digest(&built[k], &mut calls), digest, "{}: digest", name);
        assert_eq!(digest, policy_words[k], "{}: the policy's line", name);
        digests[k] = digest;
    }
    assert_eq!(at, lines.len(), "no record after the four tables");

    // The gate accepts the policy's lines and reports the same name for a flipped word of each
    // table's digest (`tblHeld`, `cp_verify.cpp:1301-1303`).
    let mut frame = Parameters::default();
    read_parameters(POLICY, &mut frame).expect("the fixture policy parses");
    assert_eq!(policy_digest_words(&frame.rest).as_slice(), policy_words.as_slice());
    let facts = TableFacts {
        lt: params.lt,
        dh: params.dh,
        theta0: params.theta0,
        cs: params.cs,
        s: params.s,
        rx: params.rx,
        has_experts: ne > 0,
    };
    assert_eq!(check_table_digests(&frame.rest, &facts), Ok(()));
    for (name, refusal) in [("tsilu0", "table-digest-silu"), ("tsig0", "table-digest-sigmoid"),
                            ("trope0", "table-digest-rope"), ("texp0", "table-digest-exp")] {
        let rest = flip_word(&frame.rest, name);
        assert_eq!(check_table_digests(&rest, &facts), Err(refusal), "mutated {}", name);
    }

    // Lines that are incomplete, interrupted or out of order are `policy-tables`; so are all 32
    // lines on a model without experts; and no lines at all is no test (`tblHeld`).
    let text = core::str::from_utf8(&frame.rest).unwrap();
    let without_texp7: Vec<u8> = text
        .split('\n')
        .filter(|l| !l.starts_with("texp7 "))
        .collect::<Vec<&str>>()
        .join("\n")
        .into_bytes();
    assert_eq!(check_table_digests(&without_texp7, &facts), Err("policy-tables"));
    let interrupted = text.replacen("tsilu1 ", "not-a-line 0\ntsilu1 ", 1).into_bytes();
    assert_eq!(check_table_digests(&interrupted, &facts), Err("policy-tables"));
    let out_of_order = text.replacen("tsilu0 ", "tsig0 ", 1).into_bytes();
    assert_eq!(check_table_digests(&out_of_order, &facts), Err("policy-tables"));
    let no_experts = TableFacts { has_experts: false, ..facts };
    assert_eq!(check_table_digests(&frame.rest, &no_experts), Err("policy-tables"));
    assert_eq!(check_table_digests(b"", &facts), Ok(()));
}

fn words8vec(v: &[&str]) -> [u32; DW] {
    assert_eq!(v.len(), DW);
    let mut out = [0u32; DW];
    for (i, w) in v.iter().enumerate() {
        out[i] = u32::from_str_radix(w, 16).unwrap();
    }
    out
}
