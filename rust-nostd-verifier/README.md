# rust-nostd-verifier

A `no_std` Rust port of the FlashProve verifier (`verifier/src/cp_verify.cpp` and the
`vf_*.h` headers). The goal is a verifier core that runs on a zkVM (RISC0/SP1) while matching the
C++ reference byte for byte.

**Status: S2a complete.** The foundation lanes are ported and parity-checked against C++:
Goldilocks field and MLE, BLAKE2b and the format's hash modes with both `q_V` counters, and
`Big`/`Real`/`Bound`/`codes`/`plan`/`accounting`. Rust already reproduces the four `result-v1`
numbers of the accepted example from a C++-dumped plan: `128.00`, `96.23`, `38`, `49`.

The proof system (`blocks/iop`, `blocks/frame`) and the verifier sub-proofs are still stubbed:
every stage returns `Internal("not-implemented")`, the host prints
`NOT CHECKED: internal-stage` and exits 5, and the stub path can never print `YES`. S2b is next;
S3 is the end-to-end gate.

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
  src/field/               gl64, F/E, multilinear helpers (S2a lane A)
  src/hash/                BLAKE2b, earlier H, modes, domains, TH (S2a lane B)
  src/numbers/             Big/Real/Bound, setting, codes, plan, accounting (S2a lane C)
fp-host/                   std binary `fp-host`
  src/main.rs              CLI, file reads, header checks, three-stage skeleton
  src/usage.txt            the static usage text, captured from the reference binary
  tests/                   unit tests, vector tests and the golden accounting test
fixtures/                  byte-for-byte example files, goldens and C++ vector dumps
scripts/parity.sh          S1 CLI/file/header parity gate
scripts/parity_field.sh    lane A: C++ field vectors -> fixtures diff -> Rust test
scripts/parity_hash.sh     lane B: Python/C++ vectors and counters -> Rust tests
scripts/parity_numbers.sh  lane C: arithmetic vectors and a C++ plan/accounting dump -> Rust tests
```

## Build and test

```sh
cd rust-nostd-verifier
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

## What S1 implements

- The command line in `cpMain()`'s order (`verifier/src/cp_verify.cpp:3274-3389`), including
  `-bits`, `-id`, `-j`, `-q`, `-show-stages`, `-no-proof-of-work`, `-next-token` and `-policy`,
  with the C++ usage text and error sentences.
- Configuration, key, request, `y`, proof and leaf-file reads with the C++ role names and
  `input-unreadable-<role>` output (status 2).
- `cpKeyHead` / `cpProofHead` (status 1 on failure), `KL-length`, `cp-entry-missing` and
  `version-unknown (policy)`.
- The three-stage skeleton (`key`, `leaf`, `request`; part calls run one), each with a fresh
  `StageState` and the C++ thread counts.
- `NOT CHECKED: internal-stage` (status 5) for the stubbed stages; the stub never prints `YES`.

Not implemented in S1 (S2/S3): the strict parameter parser, `cpPolicyHeld()`, the statement,
BLAKE2b/transcript/plan/accounting, the proof-system blocks, `result-v1`, and real proof checks.
`-plan` is accepted only as a stub and likewise ends `NOT CHECKED`.

## Parity with C++

`verifier/build.sh` needs GNU `stat`/`mv` and g++ 13 and does not run on macOS. The same
translation unit builds with Apple clang:

```sh
clang++ -O2 -std=c++17 -pthread \
  -Iverifier/src -Iblocks -Iprover \
  -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o /tmp/tl_cpp_build/cp_verify verifier/src/cp_verify.cpp
```

Then run the gate from the repository root:

```sh
rust-nostd-verifier/scripts/parity.sh
```

It looks for `/tmp/tl_cpp_build/cp_verify`, then `/tmp/fp_cpp_build/cp_verify`, and otherwise
builds the reference with the command above. It checks:

1. **21 S1 cases** listed in `fixtures/cases.tsv`: no arguments, bad options/`-bits`/`-j`/`-id`/
   `-policy`, `-bits 129`, missing policy/key/request/`y`/proof/leaf, short or wrong key/proof
   headers, a wrong policy version, a short `KL.bin`, and a missing `-plan` subcommand. C++ must
   match the stored goldens in `fixtures/cli/`; Rust must match C++ in stdout, stderr and exit
   status.
2. The **accepted example**: C++ `-q` output against `fixtures/golden_stdout.txt` (105 lines).
3. The two **negative controls**: a tampered proof byte and a wrong commitment ID, against
   `fixtures/golden_negative_*.txt`.
4. **Stub safety**: the Rust skeleton ends `NOT CHECKED: internal-stage` (exit 5) and never `YES`.

`golden_stdout.txt` contains the three `---- stage ... ---- N thread(s), X.XXX s` headings. The
seconds differ between runs; `parity.sh` normalizes only those three lines before comparing. All
other bytes, including the accounting lines, the closing four lines and `result-v1`, are compared
as they are.

## Fixtures

- `fixtures/config/`, `fixtures/ivk/`, `example.req`, `example.y`, `example.proof` and `ID.txt` are
  byte-for-byte copies from `examples/accepted-proof/` (see its `SHA256SUMS`). They are not
  generated by the Rust code.
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
  `fixtures/short-proof.bin` are the malformed inputs of the S1 cases.

## Acceptance gates

- **S1**: `cargo build --workspace`, `cargo test --workspace`, the `no_std` grep, and
  `scripts/parity.sh` (21 S1 cases + accepted/negative C++ goldens + stub safety). See
  `../docs/s1-report.md` for the recorded run.
- **S3**: the closing four lines (`commitment:`, `proof of work:`, `result-v1`, `YES`) must match
  byte for byte at exit 0, and the `accounting:` numbers (`q_V=136088`, `least-round`, …) and text
  skeleton must be recomputed by Rust and match byte for byte. The negative controls must reproduce
  `NO: proof-refused` and `NO: model-statement` with exit 1.


## S2a lanes

- **Field** (`fp-core/src/field/`): `gl64.h` arithmetic, `F`/`E` with the lazy-reduction product,
  and the MLE helpers. 18,256 C++ vectors in `fixtures/field_vectors.txt`.
- **Hash** (`fp-core/src/hash/`): BLAKE2b compression, the verifier's `H(num; w)`, `blocks/hash`
  modes (`Digest`, `Tag`, `Hasher`, leaves/vertices, chain calls), `TH`, and
  `HashCalls { f2b, blk }` for `q_V`. Vectors: RFC 7693, hashlib, 200 Python `f()` cases, 57
  repository H/TH lines, 58 mode lines, and C++/Rust counter parity.
- **Numbers/plan/accounting** (`fp-core/src/numbers/`): exact `Big`/`Real`/`Bound`, `Setting`,
  `codes`, `PlanRound`/`Planned` and `account()`. 3,785 arithmetic/code vectors plus a 23,265-line
  plan dump from `cp_with_configured()`; the Rust accounting matches all four C++ accountings
  field by field and reproduces `128.00 / 96.23 / 38 / 49`.

See `../docs/s2a-report.md` for commands, outputs and the S2b/S3 deferred items.
