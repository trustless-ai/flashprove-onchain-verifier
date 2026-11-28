# Evidence record: accepted CPU Groth16 run (2026-11-26/27)

This page is the **sanitized public record** for the completed CPU Groth16 end-to-end run
described in [the reproduction report](end-to-end-cpu-groth16.md). It records identity, artifact
hashes, local transaction hashes and the verification matrix. It contains no private repository
link, no internal absolute path and no credential.

The full raw logs and complete private archive are not included. The recorded ELF and selected
proof artifacts are available from [v1.0.0](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/tag/v1.0.0).

## Identity

| Field | Value |
|---|---|
| Guest ELF size | 12,242,912 B |
| Guest ELF SHA-256 | `f31e45a8e29cb63182045517291262422cf86692f02d1989ab7b04d1b74b860b` |
| Program vkey | `0x00077170f863a7960a725e58df8b8f3d111e58468d7d987618983ce1dc1a8f00` |
| SP1 SDK / circuit | 6.10.0 / v6.1.0 |
| Input digest | `0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392` |
| Commitment ID | `0x79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183` |
| Output hash | `0x0af488bb91e0d3b3b645a7f44f990968e50312a40ff4c88b0d606283e9b4ec43` |

## Accepted artifacts

| File | Size (B) | SHA-256 |
|---|---:|---|
| [`proof.bin`](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/proof.bin) | 8,405 | `10464eba34f906fdbd75b5a0d1d3bdb8a8406141f774de5fbb704a35f87027d8` |
| [`proof.bytes`](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/proof.bytes) | 356 | `f75d969982f1652de7f6763ac7b88e4a02f080bf23f800fcb7d9dde5643c18d7` |
| [`public_values.bin`](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/public_values.bin) | 6,711 | `1f0bdac6c80e21bece7454bf22459bb1e3e96a1830e6c77bdfa494abd07c12ef` |
| `public_values.hex` | 13,425 | `e6c8db805d7f1c776992242632d5e618ddc7e07c90d6fc59f137a47a3fc6134d` |
| [`bundle.bin`](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/bundle.bin) | 7,232 | `14c06322317057887f6b464919bae2f8b32b4acdd8869905be61a2320c0ae07a` |
| `bundle.hex` | 14,467 | `e8bafd41b7b4aafd19737ff78ee8c52307d19ba33543aa1d81b10509e3ad22af` |
| `pv.bin` | 128 | `83996c635c7acb17a9b91ff96d4b67ac93b3346dddf50fc91a8a3c8eb4686e4a` |
| `summary.json` | 959 | `89117bcce8cb77d44c8dced522f95ee7127ccf1c06b80ef4b2346b6371c76724` |

Accepted `summary.json` fields: `verdict=YES`, `call_status=0`, `proof_mode=groth16`,
`proof_bytes=356`, `public_values_bytes=6711`, `bundle_bytes=7232`,
`proof_seconds=115206.248369238`.

## Local on-chain verification

Recorded local chain: Anvil 1.10.0, chain ID 31337, RPC on loopback. Official verifier:
`sp1-contracts` v6.1.0, commit `2ac5ecbbe473421a963d67e55f182e9a36576f7c`, artifact SHA-256
`501cb171d70f4e98decfdca0b8e5f370727107f1f7e6c6dff91ca52df7d15ebe`, solc 0.8.20.

| Contract | Local address |
|---|---|
| Official `SP1Verifier` | `0x5FbDB2315678afecb367f032d93F642f64180aa3` |
| `FlashProveZKVerifier` | `0xe7f1725E7734CE288F8367e1Bb143E90bb3F0512` |
| `ExampleAgentVerifier` | `0x9fE46736679d2D9a65F0992F2272dE9f3c7fa6e0` |

| Test | Task ID | Transaction | Event `valid` | `usedTasks` after |
|---|---|---|---|---|
| Tampered proof (byte 355) | `0xaf682cb0cceddbdfda1e402e85cc48b1483e045abebb8c43a64b0ccaba4b6cc5` | `0xd49fd474d0f8b961dfb13d5685a6f652501687d63c87945eca658875e72f997c` | false | false |
| Tampered public values (byte 6710) | `0xe70a68694f9914871bef32a91f70ce4bc2ef8e6ba7ad9fd1b0fb07a48e12d078` | `0x2f7e89a1e46aefe67bc0e1e0c70031b2cc13999c2f984c037781acb68179f1ba` | false | false |
| Valid accepted bundle | `0x2523c642716b75c3a4fe706e6fc607cceba0d8d0c45b26680279e6d8273bd730` | `0x90fb7afb166549131bbdb9839e1e0ce0d221492872ed4b659ed4706fd360db75` | **true** | **true** |
| Repeat of valid task | `0x2523c642716b75c3a4fe706e6fc607cceba0d8d0c45b26680279e6d8273bd730` | `0x7326d9f500adb503112bcbca4ae0cad3a9e7cf075567c81f49aaed338f59f207` | false | true (remains) |

All four transactions had receipt status `0x1`; rejected calls emitted `valid=false` rather than
reverting. The valid call's event `verificationDigest` was independently recomputed and matched,
and the calldata's bundle, public values and proof bytes matched the accepted artifacts.

## Other key hashes

| Item | SHA-256 |
|---|---|
| On-chain `summary.json` | `38ced174e15db0a2af926d77fd4a434958028376913a18803926fb12fa598b2a` |
| `fp-pv` comparison log | `c15d1a1445f1fb65970055135471207d2b82e804b6a5d8a3e94ea83ee3e0dbc1` |
| `SHA256SUMS` of the recorded artifact set | `961be080e2649240e6ef05e54af56909948a396ad0f37d6f21597579df967f58` |
| `MANIFEST-files.tsv` | `6e83ab8fe36c495cffebe285b556d687fdec6e37876182d250fe2e4d88b429ad` |
| `MANIFEST-excluded.tsv` | `424f787630e8b8089c22387acb407e938f3b6c9121275a974fd30c3023e4e5b9` |
| `MANIFEST-management.tsv` | `a18b04490b05dd67785d53db7598eb41926de0c105f61de1e86d144a7fa898ef` |

The artifact set contains 2,594 included files and 2,605 total files including management files;
the excluded set has 434 files. The full inventory is in the private archive and is not linked
here.

## Third-party components

No third-party binaries or source packages are redistributed by this page. The run used:

| Component | Version / identity | Source |
|---|---|---|
| SP1 SDK / CLI | 6.10.0 | Succinct |
| SP1 guest image | `ghcr.io/succinctlabs/sp1:v6.10.0`, manifest `sha256:d731d3c40e4e74f606b5203d2d54fca4ee398b00a023d23cc6a6506709af4905` | Succinct container registry |
| SP1 Groth16 circuit | v6.1.0 | Succinct circuit archive |
| `sp1-contracts` verifier | v6.1.0, commit `2ac5ecbb…`, artifact `501cb171…` | Succinct |
| Foundry / Anvil | 1.10.0 | Foundry |
| Rust host / guest | 1.100.0 / 1.96.0-dev | Rust project / SP1 toolchain |
| FlashProve reference implementation and fixtures | published upstream tree / submodule `9e2bdd8` | Anthropic FlashProve |

The repository's `LICENSE`, `NOTICE`, `THIRD_PARTY.md` and the upstream components govern their
respective material; this page does not relicense any of it. Proof data (`proof.bin`/`proof.bytes`,
public values, `bundle.bin`/`bundle.hex`, `pv.bin`) and non-sensitive local receipts are generated
run data and can be public subject to the accepted-input/publication scope. The guest ELF and any
official verifier bytecode are object-code distributions that require the applicable license
texts, notices and attribution. The full raw logs and archive are not included in the release.
This page is a factual summary, not the full raw evidence.

## Verification boundary

This record supports the specific accepted example and the local Anvil run above. It does not
establish a public chain deployment, a CUDA run, input legitimacy, weight hiding, or deterministic
rebuild bytes. See the report for the full limits and reproduction commands.
