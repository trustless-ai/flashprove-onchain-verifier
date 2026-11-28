<img width="3277" height="1279" alt="trustless-ai" src="https://github.com/user-attachments/assets/76710d7f-4207-45ff-bca4-74fc88610932" />

# flashprove-onchain-verifier

**On-chain acceptance and proving tools for [FlashProve] inference proofs.** The repository
contains two stateless [ERC-8274] `IProofVerifier` implementations — one backed by an SP1 zero-knowledge
proof, one by a committee attestation — and the host/guest pipeline that produces and checks the
evidence they accept.

FlashProve makes an inference claim checkable without re-running the model: the verifier checks a
proof against a commitment and recomputes the answer from public data. This repository is the
on-chain half of that design, plus the Rust verifier and SP1 guest used to generate the proof.
It is not a model implementation and it does not decide whether an input is legitimate.

## Status

The accepted FlashProve example has been proved end to end in **CPU Groth16** mode with SP1 6.10.0
and circuit v6.1.0. The upstream `sp1-contracts` v6.1.0 verifier accepted the proof, and the
wrapper contracts accepted the resulting bundle on a **local Anvil chain**. The accepted run, its
identity, artifact hashes and negative controls are summarized in
[FlashProve to on-chain verification](docs/flashprove-to-onchain.md).

| Prover | Proof | Proof generation | Proof size | On-chain bundle size | Verification gas |
|---|---|---:|---:|---:|---:|
| CPU | SP1 Groth16 | 32 h 0 min 6 s | 356 B | 7,232 B | 486,216 gas |

The proof was generated on a 64-vCPU Intel Xeon 6982P-C machine with 512 GiB RAM. Observed peak
whole-machine memory usage was 226.97 GiB, sampled every 5 seconds; this is not a minimum memory
requirement or an exact instantaneous peak.

The accepted proof was verified on a local Anvil chain. The gas figure is for the complete
successful `ExampleAgentVerifier` transaction, including transaction input, the SP1 verifier,
and the FlashProve policy checks. Proof generation happened off-chain; on-chain verification
wall-clock time was not recorded. See the [verification overview](docs/flashprove-to-onchain.md)
for the proof path and artifacts.

This is a local verification result, not a public deployment. The recorded ELF and proof artifacts
are available from [v1.0.0](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/tag/v1.0.0);
the full raw evidence archive is not included.

## The problem

An agent can claim that a model produced an output for an input. Re-running the model to check the
claim is expensive, and trusting the agent is not verification. FlashProve turns the claim into a
proof over a committed transcript. The remaining question is what a chain should accept as
evidence. This repository answers that question with two verifier backends behind one interface,
and with the tooling that produces the evidence for the zk backend.

## Architecture

```text
application contract
  IAgentVerifier                     stateful: task, policy, authority
        |
        +--> FlashProveZKVerifier      stateless; proofSystem() = "zk/sp1"
        |         |
        |         +--> ISP1Verifier    upstream sp1-contracts v6.1.0 verifier
        |
        +--> FlashProveAttestVerifier  stateless; proofSystem() = "attestation/multisig"
                  |
                  +--> committee signatures

off-chain proof path
  inputs -> input digest -> SP1 guest (fp-core + fp-pv + sp1-zkvm)
         -> FPV1 public values -> SP1 Groth16 proof -> ABI bundle
         -> FlashProveZKVerifier.verify(inputHash, outputHash, metadata, proof)
```

| Component | Location | Role |
|---|---|---|
| Verifier contracts | [`contracts/`](contracts/) | `IProofVerifier` implementations, interfaces and an example `IAgentVerifier` |
| Rust verifier core | [`rust-verifier/`](rust-verifier/) | `fp-core`, a `no_std` Rust port of the FlashProve verifier; `fp-host` for file and CLI parity |
| SP1 guest and host tools | [`zkvm-prover/`](zkvm-prover/) | guest binary, FPV1 public-values crate (`fp-pv`), prover (`fp-prover`), vkey generator (`gen-vkey`) and host tools (`fp-hostlib`, `host-exec`) |
| Configuration | [`config/`](config/) | run configuration, vkey record and input manifest |
| Reports | [`docs/`](docs/) | measured runs, evidence record and reproduction scripts |
| Upstream reference | `upstream/FlashProve` | pinned C++ FlashProve tree used for parity tests; not linked into the guest |

The zk path uses `metadata = abi.encode(bytes32 programVKey)` and
`proof = abi.encode(bytes publicValues, bytes sp1Proof)`. The attestation path uses a
configuration hash and an EIP-712 signature bundle. Both return `false` on invalid evidence instead
of reverting. [contracts/README.md](contracts/README.md) documents the interfaces and the FPV1
block.

## Prerequisites

The recorded accepted run used Linux x86-64, 64 vCPUs, a nominal 512 GiB of RAM (495 GiB usable),
a 2 TiB disk and no GPU. The accepted proof is the expensive part: its measured peak was about
227 GiB of whole-machine memory. The run observed a minimum of 1,847 GiB free on `/`; that is an
observed free-space floor during the run, not a measured minimum required capacity. Smaller stages
run on much less.

| Requirement | Recorded version | Used for |
|---|---|---|
| Rust host toolchain | 1.100.0 | host tools and tests |
| `sp1-cli` | 6.10.0 | guest build and proof commands |
| Docker Engine | 24.0.9 (client and server, recorded) | guest build and gnark Groth16 wrap |
| SP1 guest image | `ghcr.io/succinctlabs/sp1:v6.10.0` | guest rustc 1.96.0-dev |
| SP1 gnark image | `ghcr.io/succinctlabs/sp1-gnark:v6.1.0` | Groth16 wrap |
| Groth16 circuit | v6.1.0 | proving key, circuit and verifier artifacts |
| Foundry | 1.10.0 | `forge`, `cast`, `anvil` |
| Solidity compiler | 0.8.20 for the upstream verifier; 0.8.24 for the wrappers | contract builds |

The circuit archive is a third-party download of 6,211,807,514 bytes; the report pins its SHA-256
and extraction checks. The Docker guest build supplies its own Rust toolchain; the host toolchain
does not build the guest.

## Quick start

These commands build the host tools and run the test suites. They do not create a proof and do not
need the circuit archive. Clone the repository and run them from its root:

```sh
git clone https://github.com/trustless-ai/flashprove-onchain-verifier.git

cd flashprove-onchain-verifier

cargo build --release -p fp-hostlib --bins --manifest-path zkvm-prover/Cargo.toml
cargo build --release -p host-exec --manifest-path zkvm-prover/Cargo.toml
cargo build -p fp-host --manifest-path rust-verifier/Cargo.toml

(cd rust-verifier && cargo test --workspace)
(cd zkvm-prover && cargo test --workspace)
(cd contracts && forge test)
```

A local mock smoke run exercises the whole call path without a real proof:

```sh
contracts/scripts/anvil-smoke.sh
```

A mock acceptance is not evidence that the real verifier path works. The next section runs the real
upstream verifier against a real SP1 Groth16 bundle.

## Local Anvil verification with the real verifier

The script [`docs/scripts/verify-onchain-local.sh`](docs/scripts/verify-onchain-local.sh) deploys
the upstream `sp1-contracts` v6.1.0 verifier, `FlashProveZKVerifier` and `ExampleAgentVerifier` on
a disposable local Anvil chain, then sends a valid bundle and three negative controls. It does not
create a proof.

Prepare the upstream verifier checkout at the recorded commit:

```sh
git clone https://github.com/succinctlabs/sp1-contracts.git
git -C sp1-contracts checkout 2ac5ecbbe473421a963d67e55f182e9a36576f7c
```

The recorded build used solc 0.8.20; the resulting `SP1VerifierGroth16.sol/SP1Verifier.json`
artifact had SHA-256 `501cb171d70f4e98decfdca0b8e5f370727107f1f7e6c6dff91ca52df7d15ebe`.

Set the paths and a disposable local key. `OUT` must contain, or `BUNDLE` and `SUMMARY` must point
to, a bundle and its summary from `fp-prover`. You can use a bundle you produced or download the
[accepted bundle](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/bundle.bin). The script also requires a compatible summary JSON;
the original raw summary is not among the listed release assets. For the accepted bundle,
create a minimal compatible summary using the recorded input digest, output hash, and bundle size
from the identity and artifact tables below (set `OUT` to a fresh directory first):

```sh
mkdir -p "$OUT/accepted"
curl -fL https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/bundle.bin -o "$OUT/accepted/bundle.bin"
jq -n --arg input "0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392" \
  --arg output "0x0af488bb91e0d3b3b645a7f44f990968e50312a40ff4c88b0d606283e9b4ec43" \
  '{input_digest: $input, output_hash: $output, bundle_bytes: 7232}' > "$OUT/accepted/summary.json"
```

The bundle must match the configured policy: the commitment ID in `config/flashprove.json`, a
verdict in its accepted mask, `call_status=0`, and the vkey you pass. A mock bundle is not a real
proof and cannot satisfy the valid case. The small-input Stage 4 CPU Groth16 bundle is a real
proof, but its public values carry `verdict=NO` and its smoke call does not match the accepted
commitment/verdict policy; the business wrapper emits `valid=false` and leaves the task
unconsumed. It also cannot satisfy the valid-case assertion. Use a bundle that matches the
configured accepted policy.

```sh
export ROOT="$PWD"
export OUT="/path/to/run-output"                 # holds accepted/bundle.bin and accepted/summary.json
export SP1_CONTRACTS="/path/to/sp1-contracts"
export DEPLOYER_PRIVATE_KEY="0x..."              # disposable local key; never commit it
export VKEY="0x00077170f863a7960a725e58df8b8f3d111e58468d7d987618983ce1dc1a8f00"
export PORT=8545
export RPC="http://127.0.0.1:$PORT"

docs/scripts/verify-onchain-local.sh
```

`VKEY` must match the bundle. The value above is the accepted run's vkey; set it explicitly
when verifying the accepted bundle.
For a bundle you produced, use its vkey. `COMMITMENT` and `AGENT_ID` default to
`config/flashprove.json`; override them if your configuration differs.

Use a fresh `OUT` (or copy an earlier `onchain/` directory first): the script writes
`$OUT/onchain` and does not protect existing files from being overwritten. It exits nonzero on a
mismatch. With the accepted bundle, the expected matrix is:

| Case | `VerificationCompleted.valid` | `usedTasks` after the call |
|---|---|---|
| Valid accepted bundle | `true` | `true` |
| Proof byte flipped (`proofBytes[355]`) | `false` | `false` |
| Public-values byte flipped (`publicValues[6710]`) | `false` | `false` |
| Repeat of the valid task | `false` | remains `true` |

The tamper offsets are properties of the accepted 7,232-byte bundle. The script decodes the ABI
bundle with [`docs/scripts/bundle-tools.py`](docs/scripts/bundle-tools.py), flips exactly one byte
inside the selected field, re-encodes it and checks that the other field is unchanged. It also
saves the transaction input and full receipt separately, decodes the calldata and compares the
bundle byte for byte.

### Recorded local addresses

These are deterministic addresses from the recorded local run. They are **local Anvil addresses on
chain ID 31337**, created with a disposable key; they are not a public deployment and carry no
assets.

| Contract | Address | Chain |
|---|---|---|
| Upstream `SP1Verifier` (v6.1.0) | `0x5FbDB2315678afecb367f032d93F642f64180aa3` | local Anvil, chain ID 31337 |
| `FlashProveZKVerifier` | `0xe7f1725E7734CE288F8367e1Bb143E90bb3F0512` | local Anvil, chain ID 31337 |
| `ExampleAgentVerifier` | `0x9fE46736679d2D9a65F0992F2272dE9f3c7fa6e0` | local Anvil, chain ID 31337 |

## Accepted CPU Groth16 run

| Field | Recorded value |
|---|---|
| Date | 2026-11-26/27 |
| Proof system | SP1 6.10.0, circuit v6.1.0, Groth16 |
| Backend | CPU, explicit `--mode cpu --proof-mode groth16` |
| Verdict / call status | `YES` / `0` |
| Guest cycles | 27,547,235,173 |
| Proof time | 115,206.248 s internal (32 h 0 min 6.248 s); 32 h 0 min 21 s command window |
| Program vkey | `0x00077170f863a7960a725e58df8b8f3d111e58468d7d987618983ce1dc1a8f00` |
| Input digest | `0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392` |
| Commitment ID | `0x79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183` |
| Output hash | `0x0af488bb91e0d3b3b645a7f44f990968e50312a40ff4c88b0d606283e9b4ec43` |
| Guest ELF | 12,242,912 B, SHA-256 `f31e45a8e29cb63182045517291262422cf86692f02d1989ab7b04d1b74b860b` — [download ELF](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/flashprove-guest-f31e45a8.elf) |

| Artifact | Size | SHA-256 |
|---|---:|---|
| [`proof.bin`](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/proof.bin) | 8,405 B | `10464eba34f906fdbd75b5a0d1d3bdb8a8406141f774de5fbb704a35f87027d8` |
| [`proof.bytes`](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/proof.bytes) | 356 B | `f75d969982f1652de7f6763ac7b88e4a02f080bf23f800fcb7d9dde5643c18d7` |
| [`public_values.bin`](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/public_values.bin) | 6,711 B | `1f0bdac6c80e21bece7454bf22459bb1e3e96a1830e6c77bdfa494abd07c12ef` |
| [`bundle.bin`](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/bundle.bin) | 7,232 B | `14c06322317057887f6b464919bae2f8b32b4acdd8869905be61a2320c0ae07a` |
| `summary.json` | 959 B | `89117bcce8cb77d44c8dced522f95ee7127ccf1c06b80ef4b2346b6371c76724` |

The full artifact table, configuration hashes and on-chain receipt hashes are in the
[reproduction report](docs/end-to-end-cpu-groth16.md) and the
[evidence record](docs/evidence-record.md). The `summary.json` hash above is the original accepted
file; a sanitized public copy would have a different hash because path fields are redacted.

The vkey and ELF identity above bind the accepted proof. A different ELF or vkey is a different
program identity.

## Reproducing the accepted proof

The full sequence is in [the report](docs/end-to-end-cpu-groth16.md):

- §2.3 describes the guest build with the pinned Docker image and records the ELF identity;
- §3 installs the host toolchain, SP1 CLI, circuit, Foundry and the two Docker images;
- §4 builds the host tools, points both configurations at the ELF and regenerates the vkey;
- §5 runs the six gates: identity, smoke mock, placeholder Anvil, small real Groth16, accepted
  proof, and local on-chain closure.

The accepted proof command must pass both flags:

```sh
--mode cpu --proof-mode groth16
```

The main configuration keeps `prover.mode = "cuda"`; omitting `--mode cpu` selects the CUDA path,
which this run did not exercise. Before doing anything with the vkey, verify the ELF size and
SHA-256 against the table above. If they differ, stop: you have a new artifact, and
`gen-vkey --update` would create a new program identity rather than reproduce this proof.

## Documentation

| Document | Contents |
|---|---|
| [End-to-end CPU Groth16 report](docs/end-to-end-cpu-groth16.md) | identity, six gates, commands, artifacts, resources and limits |
| [FlashProve to on-chain verification](docs/flashprove-to-onchain.md) | visual overview and recorded artifact hashes |
| [Evidence record](docs/evidence-record.md) | sanitized hashes, local receipts and the verification matrix |
| [Contracts](contracts/README.md) | interfaces, FPV1 public values and the attestation path |
| [Rust verifier](rust-verifier/README.md) | the `no_std` port, its layout and parity gates |
| [On-chain verification script](docs/scripts/verify-onchain-local.sh) | executable local Anvil closure |
| [Bundle tool](docs/scripts/bundle-tools.py) | ABI decode, tamper and re-encode |
| [Handoff record](docs/handoff.md) | historical frozen values and their provenance |

## License and attribution

The repository root is under the **Apache License 2.0** ([`LICENSE`](LICENSE)). Individual files
can carry their own license:

- Solidity files under `contracts/` declare **MIT** in their SPDX headers. This includes the
  business contracts and the vendored
  [`contracts/src/interfaces/ISP1Verifier.sol`](contracts/src/interfaces/ISP1Verifier.sol), which
  comes from `sp1-contracts` v6.1.0 and names Succinct Labs as its author.
- `sp1-zkvm` and `sp1-lib` declare **MIT OR Apache-2.0**. That statement covers those two crates;
  it is not a blanket license conclusion for every SP1 runtime object linked into the guest.
- The guest's symbol table also contains Rust `core`, `alloc`, `std`, `panic_abort` and
  `compiler_builtins`, plus `libm` (MIT), `sha2` (MIT OR Apache-2.0), `bincode` (MIT) and
  `embedded-alloc` (MIT OR Apache-2.0). The exact Rust toolchain revision and the
  `compiler_builtins` license mapping are still being pinned; the release bundle will carry the
  confirmed texts. No license conclusion is claimed here for runtime objects whose mapping is
  still open.
- The upstream `sp1-contracts` verifier sources are MIT-identified by SPDX, but that repository
  has no separate license file. The exact MIT text and copyright line for `SP1VerifierGroth16.sol`,
  `Groth16Verifier.sol` and the vendored interface remain open before any verifier bytecode is
  published. The business contracts under `contracts/` are SPDX-identified as MIT but likewise
  have no separate MIT text or copyright line in the tree.
- The Rust verifier core is a port of FlashProve; the upstream FlashProve tree is Apache-2.0 and
  its `NOTICE` is preserved byte for byte.

Existing copyright, [`NOTICE`](NOTICE) and [`THIRD_PARTY.md`](THIRD_PARTY.md) attribution is
preserved. This repository does not relicense third-party material. The guest ELF is an
object-code distribution; its distribution must retain the applicable license information.

## Known limits

- **Local chain only.** All recorded on-chain activity used a disposable local Anvil chain with
  chain ID 31337. No testnet or mainnet deployment exists, and the addresses above are not public
  infrastructure.
- **No comprehensive security or legal audit.** This repository and the recorded run have not
  undergone a comprehensive security or legal audit, and they are not certified or endorsed by
  Succinct, Anthropic or any other party. The evidence shows that one accepted example verified
  under the stated versions; it is not a general security claim.
- **Evidence scope.** The full raw logs and private archive are not included in the release. Exact
  reproduction of the accepted proof requires the recorded ELF; a rebuild is a new identity until
  its vkey is regenerated and bound.
- **No byte-for-byte rebuild guarantee.** The build command and image identify the recorded
  artifact. Compiler, path and link-order differences can change the ELF bytes.
- **Single run.** The record describes one run on one machine. It is not an independent
  reproduction and does not establish that another host reproduces the same bytes or timings.
- **CPU only.** The accepted run used the CPU prover. The CUDA path was not exercised by this
  proof, and no performance claim is made for it.
- **Fixture scope.** The accepted inputs are the upstream FlashProve example fixtures. The run
  does not establish input legitimacy, weight hiding or model quality.

## Documentation note

This README is a full rewrite for external readers. It replaces the earlier status banner and
PR-specific notes; it does not remove or relicense any third-party attribution. `LICENSE`,
`NOTICE`, `THIRD_PARTY.md` and the upstream notices remain in force, and the historical record is
kept in [docs/handoff.md](docs/handoff.md) and the
[reproduction report](docs/end-to-end-cpu-groth16.md).

## Contributing

This repository is one project under [trustless-ai](https://github.com/trustless-ai), an open home
for standards, reference implementations and live proofs that make AI claims checkable by
recomputation rather than by trust. Bug reports, documentation fixes, tests and independent
reproductions are welcome as pull requests. A useful contribution is an independent run on a chain
you control, with the versions and results recorded.

[ERC-8274]: https://ethereum-magicians.org/t/erc-8274-ai-inference-proof-verification/28083
[FlashProve]: https://github.com/anthropics/FlashProve
