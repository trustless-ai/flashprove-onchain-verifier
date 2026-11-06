//! One stage of the accepted call on the real fixtures: `run_stage` prints the text that the
//! C++ stage prints. The three texts are compared with `fixtures/golden_stdout.txt` by
//! `scripts/parity_e2e.sh`; this test dumps them for the first diff.

use fp_core::stage_state::StageState;
use fp_core::verifier::common::PolicyNamed;
use fp_core::verifier::run_stage::{run_stage, StageFiles, StageMode};

const POLICY: &[u8] = include_bytes!("../../fixtures/config/policy.txt");
const KL: &[u8] = include_bytes!("../../fixtures/config/KL.bin");
const LAYOUT: &[u8] = include_bytes!("../../fixtures/config/layout.txt");
const KEY: &[u8] = include_bytes!("../../fixtures/ivk/key.bin");
const ENTRY: &[u8] = include_bytes!("../../fixtures/ivk/leaf/0.bin");
const REQUEST: &[u8] = include_bytes!("../../fixtures/example.req");
const Y: &[u8] = include_bytes!("../../fixtures/example.y");
const PROOF: &[u8] = include_bytes!("../../fixtures/example.proof");
const ID: &str = include_str!("../../fixtures/ID.txt");

fn words(b: &[u8]) -> Vec<u32> {
    b.chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect()
}

#[test]
fn the_three_stages_print() {
    let kl = words(KL);
    let request = words(REQUEST);
    let y = words(Y);
    let policy = PolicyNamed::default();
    let id = ID.trim();
    let only = std::env::var("ONLY").ok();
    for (mode, entry, req, yy, proof) in [
        (StageMode::Key, None, None, None, None),
        (StageMode::Leaf, Some(ENTRY), None, None, None),
        (
            StageMode::Request,
            Some(ENTRY),
            Some(&request[..]),
            Some(&y[..]),
            Some(PROOF),
        ),
    ] {
        if let Some(o) = &only {
            if *o != mode.name() {
                continue;
            }
        }
        let files = StageFiles {
            pol: POLICY,
            layout: Some(LAYOUT),
            kl: &kl,
            key: KEY,
            entry,
            entry_number: 0,
            request: req,
            y: yy,
            odd_statement: false,
            proof,
            id_asked: id,
            asked: 128.0,
            quiet: true,
            next_token_asked: false,
            plan_only: false,
            policy: &policy,
        };
        let mut state = StageState::default();
        let out = run_stage(mode, files, &mut state);
        println!("==== {} status={} calls={} ====", mode.name(), out.status, out.calls);
        print!("{}", out.text);
        assert!(out.status == 3 || out.status == 12, "the stage did not pass: {}", out.status);
    }
}
