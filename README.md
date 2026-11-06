<img width="3277" height="1279" alt="trustless-ai" src="https://github.com/user-attachments/assets/76710d7f-4207-45ff-bca4-74fc88610932" />

# flashprove-onchain-verifier

**A stateless ERC-8274 `IProofVerifier` for FlashProve inference proofs. Deploy it once; every
agent verifier on the chain can call it.**

FlashProve checks a model's inference without re-running the model: a proof is verified against a
commitment, and the answer is recomputed from public data. This repository is the on-chain half of
that — one contract that accepts those proofs, and the toolchain that produces them.

```
   off chain                                                  on chain
   ────────                                                   ────────

   ┌────────────────────────────────┐
   │ rust-verifier/                 │  the verdict itself
   │   fp-core    no_std, no state  │  same bytes in, same answer out
   │   fp-host    CLI entry         │  as the C++ reference, byte for byte
   │   fixtures   byte-identical    │
   └───────────────┬────────────────┘
                   │ compiled into the guest
                   ▼
   ┌────────────────────────────────┐
   │ zkvm-prover/                   │  where the proof comes from
   │   guest    FPV1 public values  │
   │   fp-pv    the block layout    │
   │   host     execute / prove     │
   └───────────────┬────────────────┘
                   │ proof = abi.encode(publicValues, sp1Proof)
                   ▼
                                  ┌──────────────────────────────────┐
                                  │ contracts/                       │
                                  │   FlashProveVerifier             │
                                  │   stateless · IProofVerifier     │
                                  │   deploy once, everyone calls it │
                                  └────────────▲─────────────────────┘
                                               │ verify(inputHash, outputHash,
                                               │        metadata, proof) → bool
                                  ┌────────────┴─────────────────────┐
                                  │ your IAgentVerifier              │
                                  │ stateful · task · policy         │
                                  └──────────────────────────────────┘
```

Three components, one direction of flow: `rust-verifier` decides, `zkvm-prover` proves, `contracts`
accepts. Only the last one is deployed, and it is deployed once.

## The contract

`FlashProveVerifier` implements ERC-8274's inner layer. It takes four arguments:

```solidity
verify(
    bytes32 inputHash,       // FPV1 input digest
    bytes32 outputHash,      // FPV1 result-v1 digest
    bytes calldata metadata, // abi.encode(bytes32 programVKey)
    bytes calldata proof     // abi.encode(bytes publicValues, bytes sp1Proof)
) external view returns (bool);
```

and returns `true` only when the SP1 verifier accepts the proof for `programVKey`, and the
public-values block's two digests equal the caller's two hashes. A bad proof returns `false` rather
than reverting, so the layer above can record a failed attempt as well as a successful one.
`contracts/README.md` has the full layout, the FPV1 table and the exact hash scheme.

## Why one deployment serves everyone

ERC-8274 splits verification in two. The inner layer — `IProofVerifier` — is stateless: it holds no
agent, no task, no commitment ID and no policy, and it is implemented once by the proof-system
provider. The outer layer — `IAgentVerifier` — is stateful, is written by each application, and owns
all of the configuration: which program vkey, which commitment ID, which verdicts count, who is
authorized.

That split is what makes a single deployment useful. The program vkey arrives per call inside
`metadata`, so one `FlashProveVerifier` serves any number of agent verifiers, each with a different
circuit, without redeployment. Deploy it once, and applications point at it. ERC-8274 goes further
and says settlement contracts must not call `IProofVerifier` directly — they call an
`IAgentVerifier`, which calls this.

## The name is the product; the backend is reported

The contract is named after the product, not the proof system. What actually backs it is stated at
run time:

| Call | Value |
|---|---|
| `proofSystem()` | `"zk/sp1"` |
| `proofProfile()` | `keccak256(abi.encode(PROOF_SYSTEM, address(this).codehash))` |

`proofProfile()` is address-scoped and derived from the deployment's own bytecode, so a third party
can recompute it without trusting us. A different backend is a different deployment, with a
different `proofSystem()` and therefore a different profile. Two profile-scoped commitments taken
under different configurations are not comparable — that is why the scheme below is written down.

## What it expects from the caller

`metadata` is 32 bytes: the SP1 program vkey, abi-encoded. `proof` is two abi-encoded byte strings:
the public values the guest committed, and the SP1 proof itself.

`inputHash` and `outputHash` are defined by the backend, and ERC-8274 requires that definition to be
documented:

```
INPUT_DOMAIN     = "FlashProve/input-v1\0"
input_digest     = SHA-256(INPUT_DOMAIN ‖ length-prefixed ten inputs, in guest read order)
result_v1_digest = SHA-256(result-v1 line, newline excluded); zero when absent
```

Length prefixes keep bytes from moving between fields, and the digest is independent of SP1's
stdin encoding: a provider computes it from the files, the guest from the values it read, and both
must agree. Implementation: `zkvm-prover/fp-pv/src/inputs.rs`.

## Bringing your own agent verifier

`contracts/src/examples/ExampleAgentVerifier.sol` is one complete outer layer: it binds a
`FlashProveVerifier`, a program vkey, a commitment ID and an accepted-verdict mask, authorizes a set
of agents, consumes the task on success, and emits a digest on every call — success or failure.

It is a sample, not part of the shared deployment. Write your own with the same shape: the
verifier's job is to answer a yes/no question about a proof; everything else — which verdicts mean
"answered", whether the call status must be zero, which commitment ID your circuit uses, who may
submit — is policy, and policy belongs to you.

## What it proves, and what it does not

It proves that a proof, bound to a specific program vkey, verified under the SP1 verifier this
chain trusts, and that the block's digests equal the two hashes the caller supplied.

It does not prove that the model is the one you wanted, that the inputs are honest, that the
commitment ID belongs to your circuit, or that the task was authorized and paid for. Those are
claims about configuration and context — they belong to the `IAgentVerifier` above, or to whoever
signed the input.

## Where the proof comes from

`rust-verifier/fp-core` is the verdict: `#![no_std]` plus `alloc`, no file-scope state, derived
from the C++ reference and held to it byte for byte by the parity gates. `zkvm-prover/guest`
compiles that same core into an SP1 guest, which commits a 128-byte `FPV1` block before anything
else; `zkvm-prover/host-exec` executes or proves it — CPU and GPU backends, GPU by default. No
real proving runs here: proving is expected to run where a GPU cluster is available.

The upstream C++ reference is a submodule at `upstream/FlashProve`, pinned to
`9e2bdd8ff5bf9c62f18263d7dac189b0400b260c` (FlashProve 0.16.0, Apache-2.0). Two things come from
that tree: the accepted example under `examples/accepted-proof/`, which `rust-verifier/fixtures/`
mirrors byte for byte, and the sources the parity gates build their reference binary from. The pin
is a commit, not a branch: a change upstream shows up as a submodule diff that has to be taken
deliberately.

```sh
git submodule update --init --depth 1
cd upstream/FlashProve/examples/accepted-proof && shasum -a 256 -c SHA256SUMS
```

## Verify it yourself

Nothing below takes a figure on trust.

```sh
cd contracts && forge test                      # 32 tests, including the negative controls
contracts/scripts/anvil-smoke.sh                # the whole call path on a local anvil
cd zkvm-prover && cargo test --workspace        # the guest, the block layout, the host helpers
rust-verifier/scripts/parity.sh                 # 27 CLI cases + accepted/negative goldens
```

The verifier must print the same closing four lines as the C++ reference on the accepted proof, and
must refuse a flipped proof byte (`NO: proof-refused`) and a wrong commitment ID
(`NO: model-statement`), each with exit 1. The `no_std` gate:

```sh
grep -rn "use std\|extern crate std\|static mut" rust-verifier/fp-core/src/ \
  && echo VIOLATION || echo NO_STD_OK
```

## Layout

| Path | What it is |
|---|---|
| `contracts/` | **The deployment.** `FlashProveVerifier` (stateless, `IProofVerifier`), the FPV1 decoder, the interfaces, one example `IAgentVerifier`, the deploy and smoke scripts |
| `zkvm-prover/` | Where the proof comes from: the SP1 guest, the host driver, the benchmark guest, the `FPV1` definition |
| `rust-verifier/` | Where the verdict comes from: `fp-core` (`no_std`), the CLI host, fixtures, the parity gates |
| `config/` | The parameter set, the input manifest, the frozen verification key |
| `docs/` | The measured run records, one file per run, and `handoff.md` |
| `upstream/FlashProve` | The upstream C++ reference, a submodule pinned at `9e2bdd8` |

One dependency worth naming: `zkvm-prover/guest` reaches `fp-core` through
`../../rust-verifier/fp-core`, so the two trees stay siblings.

## Configuration, not constants

The verifier carries no built-in parameter set, and neither does the contract: a program vkey is a
per-call argument. Everything that says *which* model and *which* protocol a proof belongs to is
read at proving time from `config/` — the policy and layout files, the commitment key, the leaf
files, the input manifest naming all ten inputs with a bundle digest.

The verification key is frozen in `config/vkey.json` and tied to the guest ELF:

| Field | Value |
|---|---|
| ELF SHA-256 | `2d077855ff441449f6778a432d8cca59ff65922b1c48a766dc2ed9bca070f652` |
| ELF size | 12,245,688 bytes |
| program vkey | `0x00200f72646a715059f034051e4624c3f6940a6d2c2c4dca8aa3575c45f29464` |
| SP1 SDK / circuit | 6.10.0 / v6.1.0 |

Rebuild the guest and the key no longer matches. `docs/handoff.md` records these values with the
commands that re-derive and check them.

## Cost

| Measurement | Cycles |
|---|---|
| Verifier, whole run, after the optimization rounds | 26,564,072,573 |
| Verifier, whole run, before them | 32,385,267,062 |
| Change | −17.97% |
| Verifier, whole run, merged with the on-chain side | 27,031,196,170 (+1.76% over the optimized figure) |

These are proving costs, not gas. On-chain gas for deployment and a `verify()` call is not yet
measured; when it is, it belongs here with the chain and the verifier address it was taken on.

Each figure, the conditions it was taken under and what it does not cover are in `docs/`; the
per-round deltas are in `docs/cycle-optimization.md`.

## License

Apache License 2.0 — the same license as the FlashProve reference implementation and the SP1 zkVM.
See `LICENSE`, and `NOTICE` / `THIRD_PARTY.md` for the third-party notices.

## Joining Trustless AI

This repository is one project under [trustless-ai](https://github.com/trustless-ai), an open home
for the standards, reference implementations and live proofs that make AI claims checkable by
recomputation rather than by trust.

**The one rule:** nothing goes in that a third party can't independently verify from public data.
That is why the top of this README is a set of commands, not a claim.

- **Say hi on [Telegram](https://t.me/+P7blHRwexzAyYWZh)** — brainstorm, share ideas and meet like-minded
  builders. No commitment needed; just come and chat.
- **Grow with this project** — follow it, learn as it evolves, and step in whenever you are ready:
  open an issue, point out a bug, send a PR. Every contribution counts, and we review and respond as
  fast as we can.
- **Start your own** — have an idea that fits the vision? We'll create a repository under the org and
  hand you full control. Your project, your lead; we're here to support.

If you are here for the verifier specifically, the fastest useful contribution is an independent
run: deploy it on a chain you care about, call `verify()`, and tell us the gas figure we are still
missing.
