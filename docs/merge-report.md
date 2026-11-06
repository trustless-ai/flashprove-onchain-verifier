# On-chain merge report: the on-chain side merged into the verifier line

**Merge commit**: `de97e377` on `feat/nostd-verifier`
(`fp-nostd: merge the on-chain integration on-chain side (B1-B5) into the verifier line`).
Parents: `289dd85f` (the optimization round 3 accepted verifier line) and `61ce97d0` (`feat/s6-cpu`, B1–B5).
Merged with `--no-ff`; the source tree of the C++ verifier was not touched.

## 1. Conflict points and how they were resolved

Only **one** file conflicted: `zkvm-prover/host-exec/src/main.rs`. `zkvm-prover/guest/src/main.rs` and
`zkvm-prover/Cargo.toml` / `Cargo.lock` auto-merged (their auto-merged contents were then checked by hand,
see below); no fourth conflict appeared.

### 1.1 `zkvm-prover/host-exec/src/main.rs` (conflict)

The B side is the body: configuration file, `fp_hostlib` (`load_config`, `load_inputs`,
`vkey_record_path`/`load_vkey_record`/`check_elf`, `run_fp_host`, `expected_public_values`),
`inputs.stdin()`, the FPV1 decode and the public-value comparison. The A side's instrumentation was
transplanted into it:

- `Args.part` and a `--part <0|1|2|3>` arm in `parse_args` (values above 3 are refused); the help
  line lists it. The ELF/config/vkey handling stays B's.
- `let mut stdin = inputs.stdin(); stdin.write(&args.part);` — the guest reads `part` after the
  commitment ID, matching the guest's read order.
- `print_opcodes` (the optimization round 3 opcode histogram, top 20 plus `other`) is called on every run,
  full or partial, and `ExecutionReport` is imported from `sp1_core_executor`.
- Part mode returns after printing the stage text, with
  `host-exec: partial run (part N: key|leaf|request), no consistency comparison`. It performs no
  FPV1 decode, digest check, `fp-host` comparison or status check, as specified. The guest still
  commits the FPV1 block in part mode, built from that part's report text.

### 1.2 `zkvm-prover/guest/src/main.rs` (auto-merge, verified)

The merged file has the intended composition:

- input order ends with the commitment ID `String` and then `part: u32` (A's tail read);
- `call::Inputs` carries `part`;
- `input_digest` (fp-pv, B) is computed over the ten input values;
- commit order is FPV1 first (`io::commit_slice(&public_values)`), then `out`, then `status`, so the
  128-byte block starts at offset 0 regardless of the report length.

`fp_pv::from_report` tolerates a report without a `result-v1` line, so the part-mode FPV1 block
(computed from the partial text) is well-defined.

### 1.3 `zkvm-prover/Cargo.toml` / `Cargo.lock` (auto-merge, verified)

- Members are the union: `guest`, `host-exec`, `bench`, `fp-pv`, `hostlib`.
- The optimization round 1 release profile is retained (`lto = "fat"`, `codegen-units = 1`).
- The lock file auto-merged; the debug and release builds below resolve it without complaint.

## 2. Verification (all green)

### 2.1 Rust verifier (A line)

| Gate | Result |
|---|---|
| `cargo build --workspace` | pass |
| `cargo test --workspace` | **229 passed, 0 failed** |
| `scripts/parity.sh` | **31/31** |
| `scripts/parity_e2e.sh` | **3/3** |
| `scripts/parity_negative.sh` | **70/70**, rejection-name checklist **11/11** |
| `scripts/parity_base.sh` | **37 passed**, fp-core no_std scan pass |

### 2.2 zkvm workspace

`cargo build` and `cargo build --release` both pass; the release binaries `host-exec`, `gen-vkey`,
`fp-pv` and `fp-prover` are built. Guest:

```sh
cargo prove build -p guest --binaries guest \
  --rustflags="-Cllvm-args=-inline-threshold=1000"
```

- **ELF SHA-256** `2d077855ff441449f6778a432d8cca59ff65922b1c48a766dc2ed9bca070f652`
- **size** 12,245,688 bytes

### 2.3 vkey

`gen-vkey --config config/flashprove.json --update` rewrote `config/vkey.json`:

- **vkey** `0x00200f72646a715059f034051e4624c3f6940a6d2c2c4dca8aa3575c45f29464`
- circuit v6.1.0, sdk 6.10.0, ELF sha256 `2d077855…`, size 12,245,688
- `gen-vkey --check-elf` → **MATCH**

### 2.4 Full execute (release `host-exec`, full mode)

- **total cycles 27,031,196,170**; shards 1612; syscalls 0; exit code 0, status 0
- `result-v1` **IDENTICAL**, `YES` **IDENTICAL**, public values (FPV1) **IDENTICAL to fp-host**;
  committed call status 0 equals fp-host's exit status 0
- FPV1 verdict `YES`, result-v1 status 0, commitment id `0x79a5a2bc…22183`,
  input digest `0xe0ea24c8…94392`
- **consistency gate PASS**

The pre-merge accepted value was 26,564,072,573 cycles; the merged guest is **+467,123,597
(+1.76%)**. The difference is the new on-chain public-values path itself: the canonical
`input_digest` is a SHA-256 over the ten input values (the proof file dominates), and the 128-byte
FPV1 block is committed with `commit_slice` before the report. The verifier computation and its
byte-exact output are unchanged.

### 2.5 Part-mode sanity (transplanted A feature)

`host-exec --part 1` (key stage):

- status 12, **6,101,255,976 cycles**
- opcode histogram printed (20 rows plus `other`, 53 kinds)
- `host-exec: partial run (part 1: key), no consistency comparison`
- writes `STAGE PASSED WITH WORK: key`; no FPV1 or fp-host validation, as specified

### 2.6 B-line gates

- `contracts`: `forge test` → **32 passed** (13 + 10 + 9 in the three suites), 0 failed.
- `zkvm-prover/scripts/anvil-smoke.sh` → **PASS** (`the placeholder proof walked the ERC-8274 call
  path`), using the refreshed vkey record.

## 3. Red lines

- No C++ source (`blocks/`, `verifier/`, `prover/`) was modified; the source digest remains
  `93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595`.
- The consistency gate was checked on the merged guest and passed byte-exactly before this report.
- No third-party crate entered `fp-core`.
