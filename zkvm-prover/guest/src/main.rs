//! The FlashProve verifier inside SP1.
//!
//! Private input, in this order. Each byte string uses `sp1_zkvm::io::read`'s standard
//! serialization (a length, then the bytes):
//!
//!   policy.txt | layout.txt | KL.bin | key.bin | the entry file (ivk/leaf/<k>.bin) |
//!   the entry number k (u32) | the request file | the y file | the proof file |
//!   the commitment ID (a string)
//!
//! The reference call's five paths are the configuration folder (`policy.txt`, `layout.txt`,
//! `KL.bin`), the ivk folder (`key.bin` and the leaf file that the proof names), and the request,
//! y and proof files; a zkVM guest cannot read a folder, so each file is its own input.
//!
//! The public output is, in this order:
//!
//!   1. the fixed 128-byte `FPV1` block (`fp_pv::from_report`): the commitment ID, the verdict,
//!      the call's status and the SHA-256 digests of the canonical inputs and the `result-v1`
//!      line. Committed with `commit_slice`, so it starts at offset 0; this is what the ERC-8274
//!      contract decodes.
//!   2. the call's accounting, the `result-v1` line and `YES` — the same lines that `fp-host`
//!      prints on the accepted example (the consistency gate).
//!   3. the call's status (`i32`).

#![no_std]
#![no_main]

extern crate alloc;

mod call;

use alloc::string::String;
use alloc::vec::Vec;

use sp1_zkvm::io;

sp1_zkvm::entrypoint!(main);

fn bytes() -> Vec<u8> {
    io::read::<Vec<u8>>()
}

pub fn main() {
    let pol = bytes();
    let layout = bytes();
    let kl = bytes();
    let key = bytes();
    let entry = bytes();
    let entry_number = io::read::<u32>();
    let request = bytes();
    let y = bytes();
    let proof = bytes();
    let id = io::read::<String>();
    let part = io::read::<u32>();

    // Commits to the ten values above, in this order, with a domain separator; the host can
    // recompute it from the same files without SP1's stdin serialization.
    let input_digest = fp_pv::input_digest(&fp_pv::InputBundle {
        policy: &pol,
        layout: &layout,
        kl: &kl,
        key: &key,
        entry: &entry,
        entry_number,
        request: &request,
        y: &y,
        proof: &proof,
        id: &id,
    });

    let (out, status) = call::run(call::Inputs {
        pol: &pol,
        layout: &layout,
        kl: &kl,
        key: &key,
        entry: &entry,
        entry_number,
        request: &request,
        y: &y,
        proof: &proof,
        id_asked: &id,
        asked: fp_core::consts::BAR,
        part,
    });

    // First, so the report's variable length cannot move it. `commit_slice` writes the raw 128
    // bytes, with no length prefix, so the block starts at offset 0 of the public values.
    let public_values = fp_pv::from_report(&out, &id, input_digest);
    io::commit_slice(&public_values);
    io::commit(&out);
    io::commit(&status);
}
