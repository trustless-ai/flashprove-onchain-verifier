<img width="3277" height="1279" alt="trustless-ai" src="https://github.com/user-attachments/assets/76710d7f-4207-45ff-bca4-74fc88610932" />

# flashprove-onchain-verifier

**Two stateless ERC-8274 `IProofVerifier` implementations for FlashProve inference proofs — one
backed by a zk proof, one backed by a committee attestation. Deploy either once; every agent
verifier on the chain can call it.**

FlashProve checks a model's inference without re-running the model: a proof is verified against a
commitment, and the answer is recomputed from public data. This repository is the on-chain half of
that — the contracts that accept that evidence, and the toolchain that produces it.

```
   off chain                                                  on chain
   ────────                                                   ────────

   ┌──────────────────────────────────────────┐
   │ rust-verifier/                           │
   │   fp-core    no_std, no state            │
   │   fp-host    CLI entry                   │
   │   fixtures   byte-identical              │
   └─────────────────────┬────────────────────┘
                         │ compiled into the guest
                         ▼
   ┌─────────────────────┬────────────────────┐
   │ zkvm-prover/                             │
   │   guest    FPV1 public values            │
   │   fp-pv    the block layout              │
   │   host     execute / prove               │
   └─────────────────────┬────────────────────┘
                         │ zk proof → zk/FlashProveZKVerifier
                         ▼
   ┌─────────────────────┬────────────────────┐
   │ contracts/                               │
   │                                          │
   │   zk/FlashProveZKVerifier                │
   │     SP1 proof in, verdict out            │
   │                                          │
   │   attestation/FlashProveAttestVerifier   │ ◀── committee signatures arrive from
   │     committee signatures in, verdict out │      outside this repository
   │                                          │
   │   stateless · deploy once · anyone calls │
   └─────────────────────┴────────────────────┘
                         ▲
                         │ verify(inputHash, outputHash,
                         │        metadata, proof) → bool
   ┌─────────────────────┬────────────────────┐
   │ your IAgentVerifier                      │
   │   stateful · task · policy               │
   └──────────────────────────────────────────┘
```

Four components, one direction of flow: `rust-verifier` decides, `zkvm-prover` produces the
evidence, and `contracts` accepts it — through either of its two verification paths. Only
`contracts` is deployed, and it is deployed once.

## The contracts

Both live under `contracts/src/`, implement ERC-8274's inner layer, and are stateless: they hold
no agent, no task and no verdict policy. An `IAgentVerifier` — written by the application, stateful,
holding all of the configuration — wraps either one, which is what lets a single deployment serve
any number of applications. ERC-8274 goes further and says settlement contracts must not call
`IProofVerifier` directly: they call an `IAgentVerifier`, which calls this.

| Path | Contract | `proofSystem()` | Evidence it accepts |
|---|---|---|---|
| `zk/` | `FlashProveZKVerifier` | `"zk/sp1"` | an SP1 proof over FPV1 public values |
| `attestation/` | `FlashProveAttestVerifier` | `"attestation/multisig"` | signatures from a pre-approved committee |

Both take the same four arguments:

```solidity
verify(
    bytes32 inputHash,       // commitment to the model input
    bytes32 outputHash,      // commitment to the model output
    bytes calldata metadata, // deployment-time configuration, held by the IAgentVerifier
    bytes calldata proof     // per-inference evidence
) external view returns (bool);
```

`FlashProveZKVerifier` answers true only when the SP1 verifier accepts the proof for `programVKey`,
and the public-values block's two digests equal the caller's two hashes.

`FlashProveAttestVerifier` is the committee path: a set of pre-approved signers attests that a given
input produced a given output, and the contract accepts the inference once enough distinct signers
signed the same attestation. The interface, the deployment configuration and the guards are final;
the attestation preimage and the signature bundle encoding carry TODO markers for the committee
design owner. The guarantee rests on the committee being honest and independent, not on a proof
system.

Neither path reverts on bad evidence: both return `false`, so the layer above can record a failed
attempt as well as a successful one. `contracts/README.md` has the FPV1 block and both hash schemes.

## Using it

`metadata` is 32 bytes on both paths — the SP1 program vkey on the zk path, a configuration hash on
the attestation path. `proof` is two abi-encoded byte strings on the zk path (the public values the
guest committed, then the proof itself); on the attestation path it is the committee's signature
bundle.

`inputHash` and `outputHash` are defined by the backend, and ERC-8274 requires that definition to be
documented:

```
INPUT_DOMAIN     = "FlashProve/input-v1\0"
input_digest     = SHA-256(INPUT_DOMAIN ‖ length-prefixed ten inputs, in guest read order)
result_v1_digest = SHA-256(result-v1 line, newline excluded); zero when absent
```

Length prefixes keep bytes from moving between fields, and the digest is independent of SP1's stdin
encoding: a provider computes it from the files, the guest from the values it read, and both must
agree. Implementation: `zkvm-prover/fp-pv/src/inputs.rs`.

`contracts/src/examples/ExampleAgentVerifier.sol` is one complete outer layer: it binds a verifier,
a program vkey, a commitment ID and an accepted-verdict mask, authorizes a set of agents, consumes
the task on success, and emits a digest on every call. It is a sample, not part of the shared
deployment — which verdicts count, which commitment ID, who may submit, all of that is policy, and
policy belongs to you.

Everything above can be checked locally:

```sh
cd contracts && forge test          # 46 tests, including the negative controls
contracts/scripts/anvil-smoke.sh    # the whole call path on a local anvil
cd zkvm-prover && cargo test --workspace
rust-verifier/scripts/parity.sh     # the CLI parity gates against the C++ reference
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
| `contracts/` | **The deployment.** Two stateless `IProofVerifier` paths — `zk/FlashProveZKVerifier` and `attestation/FlashProveAttestVerifier` — plus the FPV1 decoder, the interfaces, one example `IAgentVerifier`, the deploy and smoke scripts |
| `zkvm-prover/` | Where the proof comes from: the SP1 guest, the host driver, the benchmark guest, the `FPV1` definition |
| `rust-verifier/` | Where the verdict comes from: `fp-core` (`no_std`), the CLI host, fixtures, the parity gates |
| `config/` | The parameter set, the input manifest, the frozen verification key |
| `docs/` | The run records, one file per run, and `handoff.md` |
| `upstream/FlashProve` | The upstream C++ reference, a submodule pinned at `9e2bdd8` |

One dependency worth naming: `zkvm-prover/guest` reaches `fp-core` through
`../../rust-verifier/fp-core`, so the two trees stay siblings. The verification key is frozen in
`config/vkey.json` and tied to the guest ELF — rebuild the guest and the key no longer matches;
`docs/handoff.md` records the values and the commands that re-derive them.

## Contribution

This repository is one project under [trustless-ai](https://github.com/trustless-ai) — an open home
for the standards, reference implementations and live proofs that make AI claims checkable by
recomputation rather than by trust. How the organisation works, and what else lives in it, is in the
[org README](https://github.com/trustless-ai).

- **Open a PR.** A bug, a doc fix, a test, a better hash scheme — every contribution counts, and we
  review as fast as we can. One rule, the same as the org's: nothing goes in that a third party
  cannot independently verify from public data.
- **Talk it through on [Telegram](https://t.me/+P7blHRwexzAyYWZh).** Brainstorm, share ideas, meet
  the people building this. No commitment needed.

The most useful contribution right now is an independent run: deploy the verifier on a chain you
care about, call `verify()`, and send us the gas figure we are still missing.

## License

Apache License 2.0 — the same license as the FlashProve reference implementation and the SP1 zkVM.
See `LICENSE`, and `NOTICE` / `THIRD_PARTY.md` for the third-party notices.
