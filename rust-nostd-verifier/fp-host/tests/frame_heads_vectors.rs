//! The configuration digest of the accepted example, compared with the reference binary's `h_par`
//! (`fixtures/golden_stdout.txt:96`), from `blocks/frame/heads.h`.

use std::fs;
use std::path::Path;

use fp_core::frame::heads::configuration_digest;
use fp_core::hash::calls::HashCalls;

fn digest_bytes_hex(d: &fp_core::hash::modes::Digest) -> String {
    let mut s = String::new();
    for w in d.w {
        for b in w.to_be_bytes() {
            s.push_str(&format!("{b:02x}"));
        }
    }
    s
}

#[test]
fn configuration_digest_matches_the_reference_h_par() {
    let at = Path::new(env!("CARGO_MANIFEST_DIR")).join("../fixtures/config");
    let policy = fs::read(at.join("policy.txt")).unwrap();
    let layout = fs::read(at.join("layout.txt")).unwrap();
    let kl = fs::read(at.join("KL.bin")).unwrap();
    let files: [&[u8]; 3] = [&policy, &layout, &kl];
    let mut calls = HashCalls::new();
    let d = configuration_digest(&files, &mut calls);
    assert_eq!(
        digest_bytes_hex(&d),
        "0adb76eef05acef273d2b9a9adc0aa985a2cfcfa64b52f4cbca9b63b565a53b2",
        "configuration digest, words {:?}",
        d.w
    );
}
