# Proving readiness report: the on-chain side, ready

on-chain side makes everything on the SP1 path ready except the real proving run, which belongs to a
machine with a GPU. The guest's public output now carries a fixed 128-byte block (`FPV1`) with the
commitment ID, the verdict and the digests of the canonical inputs and the `result-v1` line; an
ERC-8274 verifier pair binds that block on chain; a driver produces proofs in CPU, CUDA or mock
mode from one configuration file; and a handoff page gives the GPU member the frozen hashes, the
commands and the expected outputs.

Nothing here changes the C++ verifier, the protocol, `fp-host`'s printed lines, or the branch's
baseline run consistency gate.

## 1. What landed

| Task | Where | Content |
|---|---|---|
| B1 | `zkvm/fp-pv` (schema), `zkvm/hostlib/src/bin/gen-vkey.rs`, `zkvm/config/vkey.json` | `client.setup(elf)` → `SP1VerifyingKey::bytes32`; the record holds the ELF path, size and SHA-256, the SP1 SDK and circuit versions, the on-chain vkey and the Poseidon2 digest. `--update`, `--check` (full re-derivation) and `--check-elf` (hash only). |
| B2 | `zkvm/fp-pv/src/{pv,inputs,sha256}.rs`, `zkvm/guest/src/main.rs`, `zkvm/host-exec/src/main.rs`, `zkvm/config/input-manifest.json` | The `FPV1` block and the canonical input digest; the guest commits the block first with `commit_slice` (offset 0), then the unchanged report text, then the status; `host-exec` rebuilds the same block from `fp-host`'s stdout, requires byte equality, and requires the committed call status to equal `fp-host`'s exit status. `fp-pv manifest` freezes the nine input files and `--check` verifies them on another machine. |
| B3 | `zkvm/contracts/` | ERC-8274 `IProofVerifier` (`SP1ProofVerifier`) and `IAgentVerifier` (`FlashProveAgentVerifier`), the vendored SP1 verifier interface, the `FPV1` decoder, a mock SP1 verifier, tests, a production deploy script and an anvil smoke script. |
| B4 | `zkvm/hostlib/src/bin/fp-prover.rs` | CPU / CUDA / mock backends behind one config; `cuda` is the config default; `--plan` validates without `setup`; proofs are verified locally and written with public values, `pv.bin` and an ABI-ready bundle. |
| B5 | `zkvm/docs/handoff.md` | The no-names handoff: frozen hashes, requirements, build/prove/verify steps, outputs, resource estimates and limits. |
| support | `zkvm/hostlib`, `zkvm/config/flashprove.json`, `zkvm/config/flashprove.smoke.json`, `zkvm/config/flashprove.bench.json`, `zkvm/scripts/{anvil-smoke,deploy,s6-check}.sh` | One configuration-driven loader for the ELF, the ten inputs, the fp-host reference and the chain parameters; scripts for the local deployment, the production deployment and the gates. |

## 2. The public values

`FPV1` is 128 bytes, committed as raw bytes before anything else:

| offset | size | field |
|---|---|---|
| 0 | 4 | magic `FPV1` |
| 4 | 2 | schema version 1, big-endian |
| 6 | 2 | reserved, zero |
| 8 | 1 | verdict: 1 YES, 2 WITHIN_LIMITS, 3 NO, 4 NOT_A_VERIFICATION, 5 NOT_CHECKED |
| 9 | 1 | reserved, zero |
| 10 | 2 | the call's status, big-endian |
| 12 | 4 | the `status=` field of `result-v1`, big-endian |
| 16 | 32 | commitment ID (the ID in the `result-v1` line, else the asked ID) |
| 48 | 32 | SHA-256 of the canonical input bundle |
| 80 | 32 | SHA-256 of the `result-v1` line, newline excluded (zero if there is no line) |
| 112 | 16 | reserved, zero |

The canonical input digest is `SHA-256("FlashProve/input-v1\0" || len‖policy ‖ len‖layout ‖
len‖KL ‖ len‖key ‖ len‖entry ‖ entry_number(u32 LE) ‖ len‖request ‖ len‖y ‖ len‖proof ‖
len‖id)`. It does not depend on SP1's stdin serialization, so a provider computes it from the
files, the guest computes it from the values it read, and they must agree. `fp-pv manifest` prints
the nine files with root-relative paths, their sizes, their SHA-256 values, the leaf number and the
bundle digest. `zkvm/config/input-manifest.json` is the accepted example's frozen manifest;
`fp-pv manifest --check zkvm/config/input-manifest.json` must print `MATCH`. The check ignores the
path strings, so the provider's copy may live elsewhere and the files are compared by name, size
and SHA-256. This is how the two sides agree on the bytes before a proof.

`from_report` derives the block from the report text alone, so the guest and `fp-host` use the same
function; the only difference is where the text comes from. On the accepted example the block is:

```
0x46505631000100000100000000000000
  79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183
  e0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392
  0af488bb91e0d3b3b645a7f44f990968e50312a40ff4c88b0d606283e9b4ec43
  00000000000000000000000000000000
```

The Rust ABI encoder (`fp-pv bundle`) was checked byte-for-byte against
`cast abi-encode "f(bytes,bytes)"`: identical.

## 3. The contracts

```
Settlement (IAgentVerifiable)
  └── FlashProveAgentVerifier   binds: commitment ID, accepted-verdict mask, status rule,
        │                              authorized agents, program vkey metadata
        └── SP1ProofVerifier    calls the SP1 verifier on abi.encode(publicValues, proof),
              │                 then requires the block's input/result digests to equal the
              │                 caller's inputHash/outputHash
              └── ISP1Verifier  (the deployed SP1 verifier; MockSP1Verifier in local tests)
```

The wrapper's `verify(taskId, agentId, inputHash, outputHash, proof)`:

- refuses a used task or an unauthorized agent;
- calls the inner verifier and requires `valid`;
- decodes the block, and requires the configured commitment ID, a verdict whose bit is set in the
  accepted mask, `callStatus == 0` when configured, and the caller's input/output digests;
- consumes the task on success;
- emits `VerificationCompleted` on every call, passing or failing, with the ERC-8274 preimage, and
  returns `verificationDigest = keccak256(abi.encode(taskId, agentId, inputHash, outputHash, valid,
  agentProofProfile, block.timestamp, abi.encodePacked(address(this)), abi.encode(block.chainid)))`.

`agentProofProfile = keccak256(abi.encode(verifierAddress, verifier.proofProfile(),
keccak256(metadata)))`, as the ERC requires.

All parameters come from the JSON configuration: `chain.commitment_id`,
`chain.program_vkey` (or the vkey record), `chain.accepted_verdicts`,
`chain.require_status_zero`, `chain.authorized_agents`, `chain.rpc_url`, and
`chain.sp1_verifier`. The deployment scripts read them; no address or ID is in the Solidity.

## 4. Evidence

### B1 — the vkey

The ELF built by the optimization round 1/optimization round 2 configuration plus this phase's public-values block:

```
gen-vkey: ELF .../riscv64im-succinct-zkvm-elf/release/guest (12184776 bytes,
  sha256 0c78b659f7e7df5a8bb84675a5cac5e3c40242fdf5fc077667da93e2345dd30d)
gen-vkey: sp1 circuit v6.1.0, sdk 6.10.0,
  vkey 0x007991cd508039250725758bafb93d0173397e4743679884dfd7cae0ca21d0aa
```

The record (`zkvm/config/vkey.json`) also carries the Poseidon2 digest
`0x3cc8e6a8200e494164aeb1757b93d01719cbf23a0d9e62133faf95c14a21d0aa` and the eight 32-bit
words. `gen-vkey --check-elf` prints `MATCH` for this ELF.

**`setup` cost**: 16 min 36 s wall on a loaded 10-core Mac (6,475 s user time, 652% CPU). This is
the one-time ELF → vkey derivation; `fp-prover` repeats it at proving start.

### B2 — the guest runs and matches `fp-host`

`host-exec` executes the guest with SP1's CPU executor (no proving) on the accepted example and
compares:

- the `result-v1` line and `YES` with `fp-host` (the baseline run gate, unchanged);
- the guest's `FPV1` block with the block rebuilt from `fp-host`'s stdout and the same files;
- the committed call status with `fp-host`'s exit status — an independent check of
  `from_report`'s verdict-to-status mapping, which the blocks alone cannot catch.

```
host-exec: sp1 circuit v6.1.0, guest ELF .../riscv64im-succinct-zkvm-elf/release/guest (12184776 bytes, sha256 0c78b659f7e7df5a8bb84675a5cac5e3c40242fdf5fc077667da93e2345dd30d)
host-exec: vkey 0x007991cd508039250725758bafb93d0173397e4743679884dfd7cae0ca21d0aa
host-exec: input digest 0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392
host-exec: execute 496.67 s, guest exit code 0, status 0
host-exec: total cycles 27547235173
host-exec: shards 1642 (estimate ceil(cycles / shard_size), shard_size 16777216; the executor also splits at the trace-area thresholds)
host-exec: syscalls 0
host-exec: memory 0 addresses touched, 8153981611208 bytes of execution record
host-exec: public output (6571 bytes):
  ...: the end-to-end report, unchanged and byte-identical to fp-host's (omitted here)
  result-v1 status=0 claim=exact-match id=79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183 bits=128 work=32 work-rounds=38 least-round=128.00 least-round-without-work=96.23 commitment-assumed-rounds=49 record=1 r=60 e=64 T=64 tokens=61..63 y=yes policy=exact-match C=256 theta=256 cap=0 s=16 sh=8 sT=4 F=24 above-clip=0 leaf=0 stages=key,leaf,request dw=8 build=93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595
  YES
host-exec: public values FPV1 verdict=YES status=0 result-v1-status=0 id=0x79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183 input=0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392 result=0x0af488bb91e0d3b3b645a7f44f990968e50312a40ff4c88b0d606283e9b4ec43
host-exec: fp-host exit status 0, committed call status 0
host-exec: result-v1 IDENTICAL
host-exec: YES IDENTICAL
host-exec: public values IDENTICAL to fp-host
host-exec: PASS (public values, result-v1, YES and the call status match fp-host; vkey 0x007991cd508039250725758bafb93d0173397e4743679884dfd7cae0ca21d0aa matches the ELF)
```

The execute took 496.67 s on the same 10-core Mac (874.93 s in an earlier run under load; the
cycle count is identical). The guest now runs 27,547,235,173 cycles:
27.08 G at optimization round 2 plus about 0.47 G (1.7%) for the canonical input digest, which the guest computes
with SHA-256 over the 5.8 MB of input files. The baseline run gate is about the printed lines, not the cycle
count, so this addition is the only cost of B2 inside the zkVM.

The two digests were also recomputed outside Rust, so the scheme is not merely self-consistent
between two Rust call sites: a Python `hashlib`/`struct` script over the same nine files reproduces
the input digest `e0ea24c8…3294392`, and `shasum -a 256` of the `result-v1` line (newline excluded)
reproduces `0af488bb…b4ec43`.

The input convention is frozen in `zkvm/config/input-manifest.json` (root-relative paths, per-file
sizes and SHA-256 values, the leaf number and the bundle digest). On the same files:

```
fp-pv: MATCH (9 files, leaf 0, input digest 0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392)
```

### B3 — contracts and anvil

`forge test` (no third-party Solidity dependency):

```
Ran 3 test suites: 32 tests passed, 0 failed, 0 skipped (32 total tests)
```

- 9 decoder tests (magic, version, reserved bytes, verdict range, trailing bytes, big-endian
  status fields);
- 10 `SP1ProofVerifier` tests (valid bundle, wrong input/output, wrong vkey, inner rejection,
  malformed metadata/bundle/block, profile, ERC-165);
- 13 wrapper tests (acceptance, single-use task, unauthorized agent, wrong commitment ID,
  unaccepted verdict, configured mask, nonzero status, wrong digests, inner rejection, malformed
  proof, agent profile, ERC-165, exposed binding check).

The anvil smoke, with the real vkey record and a placeholder proof:

```sh
ANVIL_PORT=8548 zkvm/scripts/anvil-smoke.sh
```

```
== read the deployment parameters from .../zkvm/config/flashprove.json ==
  program vkey    0x007991cd508039250725758bafb93d0173397e4743679884dfd7cae0ca21d0aa
  commitment id   0x79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183
  accepted mask   6
  status zero     true
  agent           0x00000000000000000000000070997970c51812dc3a010c7d01b50e0d17dc79c8
== compute the public values and the placeholder bundle ==
  bundle 578 hex characters
== start anvil on port 8548 ==
== deploy and call through forge script ==
No files changed, compilation skipped
Script ran successfully.
...
ONCHAIN EXECUTION COMPLETE & SUCCESSFUL.
Transactions saved to: .../zkvm/contracts/broadcast/AnvilSmoke.s.sol/31337/run-latest.json
anvil-smoke: PASS (the placeholder proof walked the ERC-8274 call path)
```

The production path (`Deploy.s.sol`, driven by `zkvm/scripts/deploy.sh` and the configuration's
`chain` section) was also deployed to a local anvil, with `SP1_VERIFIER` set to a placeholder
address on that chain and every other parameter read from `zkvm/config/flashprove.json`: `Script
ran successfully`, `ONCHAIN EXECUTION COMPLETE & SUCCESSFUL`, 2,011,103 estimated gas.

### B4 — the driver

`fp-prover prove --plan` on the production configuration (no setup, no proving):

```
fp-prover: ELF .../riscv64im-succinct-zkvm-elf/release/guest (12184776 bytes, sha256 0c78b659f7e7df5a8bb84675a5cac5e3c40242fdf5fc077667da93e2345dd30d)
fp-prover: vkey 0x007991cd508039250725758bafb93d0173397e4743679884dfd7cae0ca21d0aa
fp-prover: sp1 circuit v6.1.0, sdk 6.10.0
fp-prover: input digest 0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392
fp-prover: mode cuda, proof mode groth16, output .../out/zkvm/example
fp-prover: groth16 is verifiable by the SP1 verifier contract
{
  "circuit_version": "v6.1.0",
  "elf_sha256": "0c78b659f7e7df5a8bb84675a5cac5e3c40242fdf5fc077667da93e2345dd30d",
  "elf_size": 12184776,
  "input_digest": "0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392",
  "mode": "cuda",
  "on_chain": true,
  "proof_bundle": "wrapper-ready",
  "proof_mode": "groth16",
  "sdk_version": "6.10.0",
  "vkey": "0x007991cd508039250725758bafb93d0173397e4743679884dfd7cae0ca21d0aa"
}
fp-prover: PLAN ONLY (no setup, no proving)
```

A build without the CUDA feature refuses `mode = cuda` before `setup`:

```
fp-prover: this binary was built without the `cuda` feature; on the GPU machine build
`cargo build --release -p fp-hostlib --bin fp-prover --features cuda`, or choose
--mode cpu / --mode mock locally
```

The CPU smoke with tiny inputs (`flashprove.smoke.json`, `--mock`) exercises configuration →
ELF/vkey check → stdin → setup → execute → mock proof → local verify → `pv.bin` → bundle:

```
fp-prover: ELF .../riscv64im-succinct-zkvm-elf/release/guest (12184776 bytes, sha256 0c78b659f7e7df5a8bb84675a5cac5e3c40242fdf5fc077667da93e2345dd30d)
fp-prover: vkey 0x007991cd508039250725758bafb93d0173397e4743679884dfd7cae0ca21d0aa
fp-prover: sp1 circuit v6.1.0, sdk 6.10.0
fp-prover: input digest 0xab853a00f1519c738c79a5f025bd4d93deef5e10b31d4efa88d5cab9701568ca
fp-prover: mode mock, proof mode groth16, output .../out/zkvm/smoke
fp-prover: MOCK backend: the output is not a real proof and is not verifiable on chain
fp-prover: setup ...
fp-prover: setup 196.5 s, vkey checked
fp-prover: proving (groth16) ...
fp-prover: proof in 1.8 s, 0 bytes, sp1 v6.1.0
fp-prover: verified locally
fp-prover: public values 0x46505631000100000300000100000000... (verdict NO, id 0x0000..., 154 bytes)
fp-prover: on-chain proof 0 bytes, bundle 288 bytes
fp-prover: wrote .../out/zkvm/smoke
```

The verdict is `NO` because the smoke fixtures are synthetic zeros, not a valid call: the smoke shows
the pipeline, not an acceptance. The mock `setup` is the light node's core-only setup (196.5 s), not
the full derivation a real prover repeats (16 min 36 s), and it still produced the recorded vkey.
The artifacts show the intended shape: `public_values.bin` 154 bytes (128-byte block + 26-byte
report), `pv.bin` 128 bytes, `bundle.bin` 288 bytes, `proof.bytes` empty (a mock Groth16 proof has
no bytes). This run first exposed a driver bug: `proof_mode = "compressed"` reached
`SP1ProofWithPublicValues::bytes`, which panics for non-on-chain proof types. The driver now asks
only Plonk/Groth16 for those bytes and writes `proof.bin` and the public values alone for
`core`/`compressed`; the smoke configuration uses `groth16`.

### The configuration-only program switch

`zkvm/config/flashprove.bench.json` names a different guest (the optimization round 2 BLAKE2b benchmark) and its
own `vkey.bench.json`; no source file changes. Running `gen-vkey` with it produces a different
record:

```
gen-vkey: ELF .../riscv64im-succinct-zkvm-elf/release/bench (117928 bytes, sha256 663587030b61e3c72105109aff739d05ff6063fc288ffbd1c1556e01a347c861)
gen-vkey: sp1 circuit v6.1.0, sdk 6.10.0, vkey 0x00dd6cf254116e162927d04ae08fc18e97ee9e959718130064922ff69a663653
gen-vkey: wrote .../zkvm/config/vkey.bench.json (vkey 0x00dd6cf254116e162927d04ae08fc18e97ee9e959718130064922ff69a663653, ELF sha256 663587030b61e3c72105109aff739d05ff6063fc288ffbd1c1556e01a347c861)
```

The two records differ in name, ELF path, size, SHA-256, vkey and Poseidon2 digest; the only inputs
to `gen-vkey` are the configuration file's `program.elf` and `program.vkey_record`. The bench
`setup` ran the same fixed ELF → vkey derivation and took 16 min 30 s, like the production ELF's
16 min 36 s; the cost does not depend on the guest's size. `gen-vkey --check-elf` with the bench
configuration prints `MATCH` for the bench record and the bench ELF, and the `git status` of the
source tree is identical before and after the switch.

## 5. What is not done

- **No real proving.** B4's proof is a mock; the GPU member runs `fp-prover` with
  `prover.mode = "cuda"` and `prover.proof_mode = "groth16"` using `zkvm/docs/handoff.md`.
- **No on-chain SP1 verifier.** The anvil deployment points `SP1ProofVerifier` at a mock that
  accepts a placeholder proof. A real deployment sets `chain.sp1_verifier` to the deployed SP1
  verifier (the Succinct gateway or a circuit-specific verifier) and uses a Groth16 proof.
- **The vkey is tied to this ELF.** The optimization round 3 cycle work changes the guest; when it lands, rebuild
  the ELF, run `gen-vkey --update`, and update the on-chain `program.vkey` before proving. The
  wrapper binds the vkey through `metadata`, so a stale vkey simply fails; it cannot accept a proof
  for another program.
- **A `YES` is `cp_verify`'s.** The Lean soundness proof covers the Lean verifier for exact-match
  claims; the C++ verifier and the CUDA prover follow the same protocol and are tested against it.
  The wrapper adds the on-chain binding, not a new soundness proof. Weight hiding is out of scope
  (`guide/weight-hiding.md`).
- **ERC-8274 is not final.** The wrapper follows the current text, including `block.timestamp` in
  `verificationDigest`. If the final ERC changes that preimage, `FlashProveAgentVerifier.verify`,
  the event and the tests must change with it; this is the interface-layer alignment to revisit
  when the standard is final.

## 6. Files

New: `zkvm/fp-pv/`, `zkvm/hostlib/`, `zkvm/config/` (including the frozen
`input-manifest.json`), `zkvm/contracts/`, `zkvm/fixtures/smoke/`, `zkvm/scripts/`,
`zkvm/docs/handoff.md`.

Changed: `zkvm/guest/src/main.rs` (commits the block first), `zkvm/guest/Cargo.toml`,
`zkvm/host-exec/src/main.rs` (configuration, block comparison, vkey check),
`zkvm/host-exec/Cargo.toml`, `zkvm/Cargo.toml` (members), `zkvm/Cargo.lock`, `.gitignore`.

Untouched: every C++ source, `fp-core` (except the optimization round 2 state already on the branch), `fp-host`'s
output, and the five reference fixtures.
