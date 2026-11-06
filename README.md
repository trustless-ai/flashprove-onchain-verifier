<img width="3277" height="1279" alt="trustless-ai" src="https://github.com/user-attachments/assets/76710d7f-4207-45ff-bca4-74fc88610932" />

# flashprove-onchain-verifier

**The FlashProve verifier in Rust — `no_std`, and runnable inside a zkVM.**

FlashProve checks a model's inference without re-running the model: a proof is verified against a
commitment, and the answer is recomputed from public data. The reference implementation is C++.
This repository is the Rust side — a verifier core that keeps `#![no_std]`, matches the C++ reference
byte for byte, and compiles into an SP1 guest program so that a proof can be checked *inside* a zkVM.

## Verify it yourself

The point of this repository is that the figures are re-derivable, not taken on trust. Nothing below
needs network access beyond `cargo`:

```sh
cd rust-nostd-verifier
cargo test --workspace          # unit, vector and golden tests
grep -rn "use std\|extern crate std\|static mut" fp-core/src/ \
  && echo VIOLATION || echo NO_STD_OK
```

`cargo test --workspace` includes the golden runs: the verifier must print the same closing four
lines as the C++ reference on the accepted proof, and must refuse a flipped proof byte
(`NO: proof-refused`) and a wrong commitment ID (`NO: model-statement`), each with exit 1.

Byte-for-byte parity against the C++ binary additionally needs the FlashProve C++ tree (the
`verifier/`, `blocks/` and `prover/` sources are not in this repository). With a reference
`cp_verify` built, the gates are:

```sh
rust-nostd-verifier/scripts/parity.sh           # 21 CLI cases + accepted/negative goldens
rust-nostd-verifier/scripts/parity_e2e.sh       # end-to-end closing lines, byte for byte
rust-nostd-verifier/scripts/parity_negative.sh  # negative controls and malformed inputs
```

## What this is

Two workspaces, kept side by side because the zkVM guest path-depends on the verifier crate:

| Path | What it is |
|---|---|
| `rust-nostd-verifier/fp-core` | The verifier itself: `#![no_std]` plus `alloc`, no file-scope state |
| `rust-nostd-verifier/fp-host` | A `std` binary that drives `fp-core` from the command line |
| `rust-nostd-verifier/fixtures` | Byte-for-byte input files, goldens and C++ vector dumps |
| `rust-nostd-verifier/scripts` | The parity gates against the C++ reference |
| `zkvm/guest` | The same verifier as an SP1 guest program |
| `zkvm/host-exec` | Executes the guest in SP1 (execution only, no proving) and checks its public output |
| `zkvm/bench` | A microbenchmark guest for cycle counts |
| `zkvm/fp-pv` | The public-values schema (`FPV1`) and the input digest convention |
| `zkvm/hostlib` | Shared host-side helpers |
| `zkvm/contracts` | The on-chain SP1 verifier wrapper and the public-values decoder |
| `zkvm/config` | The parameter set, the input manifest and the frozen verification key |
| `zkvm/docs/handoff.md` | The frozen artifacts, the input convention and the build/proving commands |
| `docs/` | The measured run records, one file per run |
| `upstream/FlashProve` | The upstream C++ reference, a submodule pinned at `9e2bdd8` |

The sibling layout is deliberate: `zkvm/guest` and `zkvm/bench` reach `fp-core` through
`../../rust-nostd-verifier/fp-core`, so the two trees must stay exactly where they are.

## Upstream pin

`upstream/FlashProve` is the upstream C++ reference as a git submodule, pinned to
`9e2bdd8ff5bf9c62f18263d7dac189b0400b260c` — the initial public release of FlashProve 0.16.0,
Apache-2.0, the same licence as this repository. Checking a proof draws two things from that tree:

- **the inputs** — `examples/accepted-proof/` holds the key, config, request, reply, proof and
  commitment ID that `rust-nostd-verifier/fixtures/` keeps byte-identical copies of;
- **the C++ reference** — `verifier/`, `blocks/` and `prover/` are the sources the parity gates build
  their reference binary from, so a full parity run needs no separate C++ checkout.

```sh
git submodule update --init --depth 1
cd upstream/FlashProve/examples/accepted-proof && shasum -a 256 -c SHA256SUMS
```

The pin is a commit, not a branch: a change upstream shows up here as a submodule diff that has to be
taken deliberately.

## Configuration, not constants

The verifier carries no built-in parameter set. Everything that says *which* model and *which*
protocol a proof belongs to is read at run time from `zkvm/config/`: the policy and layout files,
the commitment key, the leaf files, and the input manifest that names all nine inputs together with a
bundle digest. A different configuration is a different run, and the manifest is what pins it.

The verification key is frozen in `zkvm/config/vkey.json` and tied to the guest ELF: rebuild the
guest and the key no longer matches. `zkvm/docs/handoff.md` records the frozen values — the ELF hash,
its size and the vkey — with the commands that re-derive and check them.

## Proof backends

`zkvm/host-exec` drives SP1's native prover and exposes both modes: CPU and GPU (the native `cpu()`
and `cuda()` backends), with GPU as the default. No real proving is run in this repository; proving is
expected to run where a GPU cluster is available.

## Measured so far

| Measurement | Cycles |
|---|---|
| Verifier, whole run, after the optimization rounds | 26,564,072,573 |
| Verifier, whole run, before them | 32,385,267,062 |
| Change | −17.97% |
| Verifier, whole run, merged with the on-chain side | 27,031,196,170 (+1.76% over the optimized figure) |

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

- **Say hi on Telegram** — brainstorm, share ideas and meet like-minded
  builders. No commitment needed; just come and chat.
- **Grow with this project** — follow it, learn as it evolves, and step in whenever you are ready:
  open an issue, point out a bug, send a PR. Every contribution counts, and we review and respond as
  fast as we can.
- **Start your own** — have an idea that fits the vision? We'll create a repository under the org and
  hand you full control. Your project, your lead; we're here to support.

If you are here for the verifier specifically, the fastest useful contribution is an independent
run: build it, run the gates above, and tell us where your numbers differ from the ones in `docs/`.
