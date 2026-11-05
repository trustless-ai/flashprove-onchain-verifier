# S6 handoff: producing a FlashProve SP1 proof

This page is for the member who runs the GPU proving. It gives the frozen artifact hashes, the
input convention, the exact commands, the expected outputs, how to check them, and rough resource
estimates. No real proving was run when this page was written; the cycle count is measured, the
proof-time estimates are derived from it and are marked as estimates.

The on-chain side does not need the GPU: the contracts, the public-values decoder and the anvil
call path are in this repository and are tested locally.

## 1. What is frozen

| Piece | Value | Where it comes from |
|---|---|---|
| Guest program | SP1 guest built from `zkvm/guest`, `zkvm/fp-pv` and `rust-nostd-verifier/fp-core` | `zkvm/guest/` |
| ELF SHA-256 | **`0c78b659f7e7df5a8bb84675a5cac5e3c40242fdf5fc077667da93e2345dd30d`** | `zkvm/config/vkey.json` |
| ELF size | **12184776 bytes** | `zkvm/config/vkey.json` |
| SP1 circuit | **v6.1.0** | `sp1_sdk::SP1_CIRCUIT_VERSION` |
| SP1 SDK / zkVM | **6.10.0** | `zkvm/Cargo.toml`, `Cargo.lock` |
| Program vkey (on-chain) | **`0x007991cd508039250725758bafb93d0173397e4743679884dfd7cae0ca21d0aa`** | `zkvm/config/vkey.json` (`sp1.vkey_bytes32`) |
| Public-values schema | `FPV1`, 128 bytes at offset 0 | `zkvm/fp-pv/src/pv.rs`, `zkvm/contracts/src/libraries/FlashProvePublicValues.sol` |
| Input digest scheme | `FlashProve/input-v1\0` + length-prefixed fields, SHA-256 | `zkvm/fp-pv/src/inputs.rs` |
| Input files (accepted example) | `zkvm/config/input-manifest.json`: nine files, sizes, SHA-256 values, leaf 0, the bundle digest | `fp-pv manifest` |

The vkey is a function of the ELF. **If the guest changes (for example a cycle optimization), the
ELF and the vkey change.** Regenerate the record and redeploy (or reconfigure) the wrapper before
proving; a proof for one vkey is not a proof for another.

```sh
# after a program change, with the new ELF built (this runs SP1 `setup`; it is slow):
zkvm/target/release/gen-vkey --config zkvm/config/flashprove.json --update

# routine check: the ELF on disk is the one the record was generated from (hash only, fast)
zkvm/target/release/gen-vkey --config zkvm/config/flashprove.json --check-elf

# full re-derivation: recompute the vkey with SP1 `setup` and compare (also slow)
zkvm/target/release/gen-vkey --config zkvm/config/flashprove.json --check
```

Only the configuration file names the ELF, the record and the input paths; the tools have no
program-specific constants. `program.elf` and `program.vkey_record` are the two fields to change
when switching programs. `zkvm/config/flashprove.bench.json` is a worked example that points at a
different guest (the BLAKE2b benchmark) and its own record.

### The input files

The block's input digest commits to the ten values the guest reads; nine of them are files. Their
frozen description is `zkvm/config/input-manifest.json`, written by `fp-pv manifest` and checked by
`fp-pv manifest --check`:

```sh
zkvm/target/release/fp-pv manifest --check zkvm/config/input-manifest.json
# fp-pv: MATCH (9 files, leaf 0, input digest 0xe0ea24c8...)
```

The manifest records the leaf number, the canonical bundle digest, and each file's name, relative
path, size and SHA-256. The check ignores the path strings and compares names, sizes and hashes, so
the prover's copy may live elsewhere. The table below is the accepted example's manifest; for
another call, generate it from that call's configuration and give it to the prover, then run
`--check` before proving.

| file | bytes | SHA-256 | path |
|---|---|---|---|
| policy | 2,479 | `8d9ae1dda2e503550cafade93c54c1b8ecc8eb4b6dab3b843c72a478bb892d2f` | `rust-nostd-verifier/fixtures/config/policy.txt` |
| layout | 27,038 | `a0cce649d992c6f17d1e27c68ac4b900b828ff6ef0bfe8da7c2491fed9f02225` | `rust-nostd-verifier/fixtures/config/layout.txt` |
| kl | 464 | `b8fb55ed7c70c4cdc7bac01e804dd0dc79349022ba7972957c7e50a29dc974a2` | `rust-nostd-verifier/fixtures/config/KL.bin` |
| key | 1,096,408 | `123dc39e8947fd3ba838d7a1a35d587c2f0e1707d1bca9b6ed551b52bf0c2e09` | `rust-nostd-verifier/fixtures/ivk/key.bin` |
| entry | 536,952 | `c9484f50fedfaf4e28ec9d1b5d19c3cd5e97bf4582511da49f9eb5693f10e1e0` | `rust-nostd-verifier/fixtures/ivk/leaf/0.bin` |
| request | 264 | `ce700974a03d43586d66ca742f9bbc8ad45c936d03dfdb8614dd559a2780aa13` | `rust-nostd-verifier/fixtures/example.req` |
| y | 4 | `add7f2a4843f8c512c0e2875546581db11b9ba227ee008b5f719dfacb125de76` | `rust-nostd-verifier/fixtures/example.y` |
| proof | 4,145,300 | `5ed47fd101093e826a5bc833e57633e5a9237b49213c8f37cf518a3c1c8d9d99` | `rust-nostd-verifier/fixtures/example.proof` |
| id | 64 | `7854b8b0879402583fe279d0f74561331bb89438f72ba6ff7ec81932fe397220` | `rust-nostd-verifier/fixtures/ID.txt` |

Input digest: **`0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392`**. This is the
`inputHash` the wrapper's `verify` must receive; the proof's block carries the same 32 bytes.

## 2. Requirements on the proving machine

- Linux x86-64, an NVIDIA GPU (an H100 with 80 GB is the reference; a smaller card may not fit
  the shard's memory), a working NVIDIA driver and CUDA. SP1's CUDA prover is built on Linux.
- Rust (the repository's stable toolchain) and `cargo`.
- `sp1-cli 6.10.0`: `cargo install sp1-cli --version 6.10.0 --locked`
- The SP1 zkVM toolchain: `cargo prove install-toolchain` (rustc `1.96.0-dev`, targets
  `riscv64im-succinct-zkvm-elf`).
- The repository at the commit that holds the frozen artifact (branch `feat/s6-cpu`; the client
  gives the commit hash); the `bin/`, `prover/` and `zkvm/target/` trees are not required.
- The guest ELF at the path configured in `program.elf`, **or** the ability to rebuild it. A
  rebuild must reproduce the ELF hash in `zkvm/config/vkey.json`; if it does not (for example the
  source changed), stop and regenerate the record and the on-chain configuration instead of
  proving against a stale vkey.

Checks (after building the tools in §3):

```sh
cargo prove --version                      # cargo-prove sp1 ...
rustup toolchain list                      # includes `succinct`
zkvm/target/release/gen-vkey --check-elf   # MATCH against the current ELF
zkvm/target/release/fp-pv manifest --check zkvm/config/input-manifest.json
                                           # MATCH against the frozen input files
```

## 3. Build the prover

On the GPU machine only. First the tools and a CPU/mock prover (no CUDA required):

```sh
cargo build --release -p fp-hostlib --bins --manifest-path zkvm/Cargo.toml
```

Then the CUDA prover (the `cuda` feature does not build on macOS):

```sh
cargo build --release -p fp-hostlib --bin fp-prover --features cuda \
  --manifest-path zkvm/Cargo.toml
```

Without `--features cuda`, the binary builds and can prove on CPU or mock; it refuses
`prover.mode = "cuda"` with an explanatory error.

## 4. Produce a proof

Edit `zkvm/config/flashprove.json` (or copy it) so that:

- `program.elf` names the frozen ELF and `program.vkey_record` names its record;
- `inputs.*` names the five paths of the call to prove: the configuration folder (`policy.txt`,
  `layout.txt`, `KL.bin`), the ivk folder (`key.bin`, `leaf/<n>.bin`), the request, y and proof
  files, and the commitment ID file;
- `prover.mode` is `"cuda"`, `prover.proof_mode` is `"groth16"` (on-chain) and `prover.output_dir`
  is where the artifacts should go.

The leaf number is the third word of the FlashProve proof header; the loader derives it, so the
ivk folder must contain that leaf file.

Before proving, confirm the files are the client's: `fp-pv manifest --check <the client's
manifest>` must print `MATCH`, and the manifest's `input_digest` must equal the `inputHash` the
client will pass to the wrapper. The prover computes the same digest from the files and refuses to
write artifacts if the guest committed a different one.

```sh
zkvm/target/release/fp-prover prove --config zkvm/config/flashprove.json
```

`--plan` validates everything (config, ELF hash, vkey record, input digest, output paths) without
`setup` or proving. `--mock` runs the whole pipeline with a mock proof on any machine; it still
executes the guest, so use `zkvm/config/flashprove.smoke.json` (tiny inputs) for a local smoke.

## 5. Outputs

In `prover.output_dir`:

| File | Contents |
|---|---|
| `proof.bin` | `SP1ProofWithPublicValues`, bincode-serialized |
| `proof.bytes` | the on-chain proof bytes (Groth16/Plonk) |
| `public_values.bin` | raw SP1 public values: the 128-byte `FPV1` block, the report text, the call status |
| `public_values.hex` | the same, 0x-prefixed |
| `pv.bin` | the first 128 bytes, the `FPV1` block alone |
| `bundle.bin` | `abi.encode(bytes publicValues, bytes proofBytes)` — the wrapper's `proof` argument (Groth16/Plonk; core and compressed proofs write no bundle) |
| `bundle.hex` | the same, 0x-prefixed |
| `summary.json` | ELF hash, vkey, input digest, verdict, commitment ID, proof mode, sizes, elapsed |

The prover verifies the proof locally before writing these files, and refuses to write them if the
guest's committed input digest differs from the host's.

## 6. Check before sending

Off-chain, with the same inputs:

```sh
# The block the files imply, recomputed through fp-host (no SP1):
zkvm/target/release/fp-pv expected --config zkvm/config/flashprove.json

# The block inside the proof:
zkvm/target/release/fp-pv decode --file out/zkvm/example/pv.bin

# Byte-for-byte comparison:
zkvm/target/release/fp-pv check --config zkvm/config/flashprove.json \
  --pv-file out/zkvm/example/pv.bin
```

`fp-pv check` must print `MATCH`. Then check the values that matter:

- `summary.json` → `verdict` must be `YES` (or `WITHIN_LIMITS` if the deployment accepts it),
  `call_status` must be `0`, `commitment_id` must equal the commitment ID you intend to claim;
- `input_digest` must equal the `inputHash` you will pass to the wrapper;
- `output_hash` must equal the `outputHash` you will pass to the wrapper.

On-chain (the wrapper must be deployed for the same vkey; `verify` consumes the task, so send a
transaction, not `cast call`):

```sh
cast send <AGENT_VERIFIER> "verify(bytes32,bytes32,bytes32,bytes32,bytes)" \
  <TASK_ID> <AGENT_ID> <INPUT_HASH> <OUTPUT_HASH> "$(cat out/zkvm/example/bundle.hex)" \
  --rpc-url <RPC_URL> --private-key <KEY>
```

The decoded transaction receipt carries the return `(bool valid, bytes32 verificationDigest)`;
`valid` must be `true`, and `usedTasks(taskId)` becomes `true`. The `VerificationCompleted` event carries the preimage of the
digest, so any observer can recompute it:

```
keccak256(abi.encode(taskId, agentId, inputHash, outputHash, valid,
                     agentProofProfile, block.timestamp,
                     abi.encodePacked(agentVerifier), abi.encode(block.chainid)))
```

The deployment must have been made with the same `program.vkey_bytes32`, `commitment_id`,
accepted-verdict mask, status rule and agent ID; `zkvm/scripts/deploy.sh` reads all of them from
the configuration file.

## 7. Resource estimates

Measured on the accepted example at this commit:

| Figure | Value | Source |
|---|---|---|
| Guest cycles (execute) | **27,547,235,173** | `host-exec` on the accepted example |
| Shards (upper estimate) | **1642** = ceil(cycles / 2^24) | `host-exec` prints it |
| `setup` (ELF → vkey) | **16 min 36 s** on a loaded 10-core Mac (6,475 s user, 652% CPU) | `gen-vkey --update` |
| Guest ELF | **12184776 bytes** | `gen-vkey` |
| Public values | about 6.5 KB (128-byte block + report + status) | `host-exec` |

Estimates for Groth16 proving (not measured here; they follow from the cycle count and SP1's
per-shard cost, and should be replaced by the GPU member's own timings):

- **GPU memory:** 16–24 GB per proving process for a 2^24-cycle shard. One H100 80 GB can run
  several shard processes in parallel; the executor is the other memory user.
- **Host RAM:** 32–64 GB for the driver and the shard workers; more if several shards run at once.
- **Time:** SP1's CUDA core prover sustains roughly 0.5–2 MHz of RISC-V cycles per H100 in this
  version (order of magnitude; replace with the GPU member's measured throughput). The accepted
  example is 1642 shards, so one H100 takes on the order of 4–15 hours for the core
  proofs; the shards are independent, so N GPUs divide that time by about N. The recursion and
  Groth16 step adds minutes to hours on top, depending on the shard count and the machine.
  The `setup` step before proving repeats the ELF → vkey derivation: **16 min 36 s** on a loaded
  10-core CPU machine in this phase, so budget for it once per prover start.
- **Disk:** the saved Groth16 proof is small (kilobytes); the intermediate shard proofs and the
  prover's scratch space are the bulk. Reserve 50–100 GB.
- **Network:** none during proving after the toolchain and the SP1 artifacts are installed.

These numbers are order-of-magnitude. The cycle count is exact and does not depend on the GPU.

## 8. Limits

- A `YES` here is the SP1 guest's `YES`: it reproduces what `fp-host` accepts on synthetic
  fixtures. The Lean proof covers the Lean verifier for exact-match claims; the C++ verifier and
  the CUDA prover are tested against the protocol, not proved. See `guide/what-is-proved.md`.
- The wrapper binds a claim to the configured commitment ID, verdict and digests. It does not
  prove that the weights are hidden (`guide/weight-hiding.md`), nor that the input is legitimate.
- The placeholder proof used by `zkvm/scripts/anvil-smoke.sh` is not a proof. Never deploy
  `MockSP1Verifier` on a real chain; point `SP1ProofVerifier` at the deployed SP1 verifier.
- A proof is only valid for the exact ELF whose vkey is configured. Rebuilding the guest is a
  program change: regenerate `vkey.json`, redeploy or reconfigure the wrapper, then prove.
- The public values are public: the report text includes the accounting and the `result-v1` line.
  The private input (the weights-derived key, the leaf, the request, y and the FlashProve proof)
  stays private to the proof; the claim's commitment ID is public.
