//! Core unit tests for the pure core functions.
//!
//! These live in `fp-host/tests` because they use the standard test harness. `fp-core/src`
//! itself must stay free of `use std`, `extern crate std` and `static mut`.

use fp_core::consts::{
    BUILD_SOURCE_DIGEST, PROGRAM_VERSION_WORD, TAG_KEY, TAG_PROOF, VERSION_TEXT,
};
use fp_core::head::{
    cp_key_head, cp_policy_word, cp_proof_head, cp_word, version_from_text, CP_KEY_HEADW,
    CP_PROOF_HEADW,
};
use fp_core::out::{
    cp_line_of, cp_not_checked_lines, cp_reason_of, input_unreadable_line, no_line, role_name,
};
use fp_core::refusal::Refusal;
use fp_core::stage_state::StageState;

fn key_header(ver: u32) -> Vec<u8> {
    let mut h = Vec::from(*b"CPIK");
    h.extend_from_slice(&ver.to_le_bytes());
    h
}

fn proof_header(ver: u32, k: u32) -> Vec<u8> {
    let mut h = Vec::from(*b"CPPF");
    h.extend_from_slice(&ver.to_le_bytes());
    h.extend_from_slice(&k.to_le_bytes());
    h
}

#[test]
fn constants_match_the_cpp_build() {
    assert_eq!(PROGRAM_VERSION_WORD, 825_374_792);
    assert_eq!(VERSION_TEXT, "H821");
    assert_eq!(TAG_KEY, u32::from_le_bytes(*b"CPIK"));
    assert_eq!(TAG_PROOF, u32::from_le_bytes(*b"CPPF"));
    assert_eq!(CP_KEY_HEADW, 2);
    assert_eq!(CP_PROOF_HEADW, 3);
    assert_eq!(BUILD_SOURCE_DIGEST.len(), 64);
    assert!(BUILD_SOURCE_DIGEST.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)));
}

#[test]
fn cp_word_is_little_endian() {
    let b = [0x43, 0x50, 0x49, 0x4b, 0xff, 0, 0, 0];
    assert_eq!(cp_word(&b, 0), u32::from_le_bytes(*b"CPIK"));
    assert_eq!(cp_word(&b, 1), 0x0000_00ff);
}

#[test]
fn version_from_text_is_inverse_of_text() {
    for v in [PROGRAM_VERSION_WORD, 0, 0x3132_3848, 0xffff_ffff] {
        let b = v.to_le_bytes();
        assert_eq!(version_from_text(&b), v);
    }
    assert_eq!(version_from_text(b"H82"), 0);
}

#[test]
fn key_head_matches_cp_key_head() {
    let v = PROGRAM_VERSION_WORD;
    assert_eq!(cp_key_head(&key_header(v), v), Ok(()));
    assert_eq!(
        cp_key_head(&[0u8; 4], v),
        Err(Refusal::named("cp-key-length"))
    );
    let mut bad = key_header(v);
    bad[0] = b'X';
    assert_eq!(cp_key_head(&bad, v), Err(Refusal::named("cp-key-head")));
    assert_eq!(
        cp_key_head(&key_header(v), v ^ 1),
        Err(Refusal::named("cp-key-head"))
    );
}

#[test]
fn proof_head_returns_the_leaf_number() {
    let v = PROGRAM_VERSION_WORD;
    assert_eq!(cp_proof_head(&proof_header(v, 7), v), Ok(7));
    assert_eq!(
        cp_proof_head(&[0u8; 8], v),
        Err(Refusal::named("cp-proof-length"))
    );
    let mut bad = proof_header(v, 0);
    bad[0] = b'X';
    assert_eq!(cp_proof_head(&bad, v), Err(Refusal::named("cp-proof-head")));
}

#[test]
fn policy_word_accepts_only_the_served_version() {
    assert_eq!(cp_policy_word(b"version H821\nsec 128\n"), Ok(PROGRAM_VERSION_WORD));
    assert_eq!(
        cp_policy_word(b"version H999\nsec 128\n"),
        Err(Refusal::named("version-unknown (policy)"))
    );
    assert_eq!(
        cp_policy_word(b"sec 128\n"),
        Err(Refusal::named("version-unknown (policy)"))
    );
    assert_eq!(
        cp_policy_word(b"version H821"),
        Err(Refusal::named("version-unknown (policy)"))
    );
}

#[test]
fn cp_line_of_takes_the_last_matching_line() {
    assert_eq!(cp_line_of("a\nresult:x\nresult:y\n", "result:"), "y");
    assert_eq!(cp_line_of("result:first\n", "result:"), "first");
    assert_eq!(cp_line_of("result:x", "result:"), "x");
    assert_eq!(cp_line_of("a\nresult:x\n", "other:"), "");
    assert_eq!(cp_line_of("result:", "result:"), "");
}

#[test]
fn cp_reason_of_allows_only_letters_and_the_fixed_punctuation() {
    assert_eq!(
        cp_reason_of("proof: bad thing\nNO: proof-refused\n"),
        ": bad thing"
    );
    assert_eq!(
        cp_reason_of("key: a(b)-c,d.e:f; g'h i\nNO: key-refused\n"),
        ": a(b)-c,d.e:f; g'h i"
    );
    assert_eq!(cp_reason_of("entry: bad/thing\nNO: entry-refused\n"), "");
    assert_eq!(cp_reason_of("entry: bad1\nNO: entry-refused\n"), "");
    assert_eq!(cp_reason_of("NO: proof-refused\n"), "");
    assert_eq!(cp_reason_of("a\nNO: proof-refused\n"), "");
    assert_eq!(cp_reason_of("other: ok\nNO: proof-refused\n"), "");
    assert_eq!(cp_reason_of("proof: \nNO: proof-refused\n"), "");
}

#[test]
fn output_lines_match_the_cpp_text() {
    assert_eq!(no_line("model-statement"), "NO: model-statement\n");
    assert_eq!(
        input_unreadable_line("key", role_name("key"), Some("No such file or directory")),
        "input-unreadable-key: key.bin cannot be read: No such file or directory\n"
    );
    assert_eq!(
        input_unreadable_line("entry", role_name("entry"), None),
        "input-unreadable-entry: the entry file cannot be read: it is not a regular file, or the read came up short\n"
    );
    let machine = cp_not_checked_lines("why", "internal-stage");
    assert!(machine.contains(
        "the verifier itself failed: nothing has been verified."
    ));
    assert!(machine.ends_with("NOT CHECKED: internal-stage\n"));
    let own = cp_not_checked_lines("why", "G0:internal-f-table-read");
    assert!(own.starts_with("a guard of the verifier's own spoke: nothing has been verified"));
    assert!(own.ends_with("NOT CHECKED: G0:internal-f-table-read\n"));
}

#[test]
fn stage_state_defaults_match_the_cpp_globals() {
    let s = StageState::default();
    assert_eq!(s.tau, 160);
    assert_eq!(s.lidb, 22);
    assert_eq!(s.nminh, 0);
    assert_eq!(s.residual_stream_limbs, 4);
    assert_eq!(s.gate_table_input_fraction_bits, 8);
    assert_eq!(s.smax, 4095);
    assert_eq!(s.rcl, 0);
    assert_eq!(s.gcl, 0);
    assert_eq!(s.inner_threads, 1);
    assert_eq!(s.run_version_word, 0);
    assert!(!s.run_version_word_fixed);
    assert!(!s.refuse_throws);
    assert!(s.current_segment.is_none());
    assert!(s.stage_shapes_made.is_none());
    assert!(!s.stage_work_note.needed);
    assert!(!s.acct_note.formed);
    assert_eq!(s.stated_target.at, 0);
    assert_eq!(s.stated_target.hb, 0);
    assert_eq!(s.hash_calls.f2b, 0);
    assert_eq!(s.hash_calls.blk, 0);
    assert_eq!(s, StageState::default());
}
