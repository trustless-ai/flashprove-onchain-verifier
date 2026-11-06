# rust-verifier

A `no_std` Rust port of the FlashProve verifier (`verifier/src/cp_verify.cpp` and the
`vf_*.h` headers). The verifier core runs inside a zkVM (SP1) while matching the C++ reference
byte for byte.

**Status: complete.** The port covers the whole verifier, not a subset: the command line and the
file/header handling, the foundation layers (Goldilocks field and MLE, BLAKE2b with the format's
hash modes and both `q_V` counters, `Big`/`Real`/`Bound`/`codes`/`plan`/`accounting`), the proof
system (`blocks/iop`, `blocks/frame`) and the verifier sub-proofs.

Against the accepted example it prints the same closing four lines as the C++ reference — `commitment:`,
`proof of work:`, `result-v1` (`128.00`, `96.23`, `38`, `49`) and `YES` — and the `accounting:` lines
match field for field. Both negative controls return `NO`: a flipped proof byte gives
`NO: proof-refused`, a wrong commitment ID gives `NO: model-statement`, each with exit 1.

The same core is the guest program in [`../zkvm-prover`](../zkvm-prover), where it runs in the SP1 zkVM.

## Layout

```
Cargo.toml                 workspace; the only dependency is pinned libm 0.2.16
fp-core/                   #![no_std] + extern crate alloc
  src/refusal.rs           Refusal::{Named, Internal} and Result
  src/consts.rs            DW, version word, tags, build digest, exit statuses
  src/names.rs             all 304 verifier/src/vf_rejection_names.txt entries,
                           each with a C++ source pointer and a test-coverage note
  src/head.rs              cp_word / cp_key_head / cp_proof_head / cp_policy_word
  src/out.rs               cp_line_of / cp_reason_of / refusal line formatting
  src/stage_state.rs       per-stage state, including HashCalls { f2b, blk }
  src/field/               gl64, F/E, multilinear helpers
  src/hash/                BLAKE2b, earlier H, modes, domains, TH
  src/numbers/             Big/Real/Bound, setting, codes, plan, accounting
  src/verifier/            the verifier itself: stages, segments, smallness, checks
fp-host/                   std binary `fp-host`
  src/main.rs              CLI, file reads, header checks, the stage runner
  src/usage.txt            the static usage text, captured from the reference binary
  tests/                   unit tests, vector tests and the golden accounting test
fixtures/                  byte-for-byte example files, goldens and C++ vector dumps
scripts/parity.sh          CLI/file/header parity gate
scripts/parity_field.sh    field vectors: C++ dumps -> fixtures diff -> Rust test
scripts/parity_hash.sh     hash vectors and counters -> Rust tests
scripts/parity_numbers.sh  arithmetic vectors and a C++ plan/accounting dump -> Rust tests
scripts/parity_e2e.sh      end-to-end gate: the closing four lines, byte for byte
scripts/parity_negative.sh the negative controls and the malformed-input cases
```

## Build and test

```sh
cd rust-verifier
cargo build --workspace
cargo test --workspace
```

The `no_std` gate:

```sh
grep -rn "use std\|extern crate std\|static mut" fp-core/src/ && echo VIOLATION || echo NO_STD_OK
```

`fp-core` may use `core` and `alloc` only. File-scope state is forbidden; `StageState` holds what
C++ keeps in mutable globals, and each stage builds a fresh one. `cargo test` is run from
`fp-host/tests`, so the test harness's `std` never enters `fp-core/src`.

## Parity with C++

The C++ reference builds on macOS with Apple clang:

```sh
git submodule update --init --depth 1      # upstream/FlashProve, pinned at 9e2bdd8
clang++ -O2 -std=c++17 -pthread \
  -Iupstream/FlashProve/verifier/src -Iupstream/FlashProve/blocks -Iupstream/FlashProve/prover \
  -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o /tmp/fp_cpp_build/cp_verify upstream/FlashProve/verifier/src/cp_verify.cpp
```

The C++ sources (`verifier/`, `blocks/`, `prover/`) are not in this repository: they come from the
`upstream/FlashProve` submodule, pinned to the published 0.16.0 tree. With the submodule initialised,
run the gates from the repository root:

```sh
rust-verifier/scripts/parity.sh           # CLI cases + accepted/negative goldens
rust-verifier/scripts/parity_e2e.sh       # end-to-end closing lines
rust-verifier/scripts/parity_negative.sh  # negative controls and malformed inputs
```

`parity.sh` looks for `/tmp/fp_cpp_build/cp_verify`, then `/tmp/tl_cpp_build/cp_verify`, and
otherwise builds the reference with the command above. It checks:

1. **21 CLI cases** listed in `fixtures/cases.tsv`: no arguments, bad options/`-bits`/`-j`/`-id`/
   `-policy`, `-bits 129`, missing policy/key/request/`y`/proof/leaf, short or wrong key/proof
   headers, a wrong policy version, a short `KL.bin`, and a missing `-plan` subcommand. C++ must
   match the stored goldens in `fixtures/cli/`; Rust must match C++ in stdout, stderr and exit
   status.
2. The **accepted example**: C++ `-q` output against `fixtures/golden_stdout.txt` (105 lines).
3. The two **negative controls**: a tampered proof byte and a wrong commitment ID, against
   `fixtures/golden_negative_*.txt`.

`golden_stdout.txt` contains the three `---- stage ... ---- N thread(s), X.XXX s` headings. The
seconds differ between runs; `parity.sh` normalizes only those three lines before comparing. All
other bytes, including the accounting lines, the closing four lines and `result-v1`, are compared
as they are.

## Fixtures

- `fixtures/config/`, `fixtures/ivk/`, `example.req`, `example.y`, `example.proof` and `ID.txt` are
  byte-for-byte copies from `upstream/FlashProve/examples/accepted-proof/`, the pinned upstream
  submodule (which carries its own `SHA256SUMS`). They are not generated by the Rust code.
- `fixtures/vf_rejection_names.txt` is a copy of `verifier/src/vf_rejection_names.txt`; the test in
  `fp-host/tests/names_test.rs` checks that `fp_core::names::REJECTION_NAMES` has the same names in
  the same order (304 entries) and that every entry has a source and a test note.
- `fixtures/golden_stdout.txt` is the reference `-q` run of the accepted example.
- `fixtures/golden_negative_tampered.txt` is the last three lines after flipping byte 2072650 of
  `example.proof` (`^= 0x01`): `NO: proof-refused`, exit 1.
- `fixtures/golden_negative_wrong_id.txt` is the three-line output for `-id` with the last hex
  digit changed from `3` to `4`: `NO: model-statement`, exit 1.
- `fixtures/config-badversion/`, `fixtures/config-shortkl/`, `fixtures/ivk-no-leaf/`,
  `fixtures/bad-key.bin`, `fixtures/short-key.bin`, `fixtures/bad-proof.bin` and
  `fixtures/short-proof.bin` are the malformed inputs of the CLI cases.

## Acceptance

- **CLI and file handling**: `cargo build --workspace`, `cargo test --workspace`, the `no_std` grep,
  and `scripts/parity.sh` (21 CLI cases + accepted/negative C++ goldens).
- **End to end**: the closing four lines (`commitment:`, `proof of work:`, `result-v1`, `YES`) must
  match byte for byte at exit 0, and the `accounting:` numbers (`q_V=136088`, `least-round`, …)
  must be recomputed by Rust and match byte for byte. The negative controls must reproduce
  `NO: proof-refused` and `NO: model-statement` with exit 1.
- **Foundation layers**: 18,256 C++ field vectors (`fixtures/field_vectors.txt`); RFC 7693,
  hashlib, 200 Python `f()` cases, 57 repository H/TH lines, 58 mode lines and C++/Rust counter
  parity for the hash layer; 3,785 arithmetic/code vectors plus a 23,265-line plan dump for
  arithmetic, plan and accounting.
