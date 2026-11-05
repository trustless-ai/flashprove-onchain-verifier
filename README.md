# FlashProve Rust Verifier (no_std, SP1 zkVM)

The FlashProve verifier ported to `no_std` Rust and packaged as an SP1 zkVM guest, together with
the host tools that execute it, benchmark it, and derive and bind the on-chain verification keys.

This repository holds the Rust side only. The original C++ verifier is not included: the Rust
verifier lives in `rust-nostd-verifier/` and the zkVM plumbing in `zkvm/`. Imported from
FlashProve at commit `6d3bfc56`.

## Layout

| Path | What it is |
|---|---|
| `rust-nostd-verifier/fp-core` | The `no_std` verifier core: Big/Real arithmetic, plan building, checking |
| `rust-nostd-verifier/fp-host` | Host-side driver used by tests and parity checks |
| `zkvm/guest` | The SP1 guest program (the verifier running inside the zkVM) |
| `zkvm/host-exec` | SP1 host: execute, prove (CPU or GPU backend), verify |
| `zkvm/fp-pv` | Public-values schema (`FPV1`) and the input digest convention |
| `zkvm/hostlib` | Shared host helpers |
| `zkvm/bench` | Cycle benchmark |
| `zkvm/contracts` | On-chain SP1 verifier wrapper and the FlashProve public-values decoder |
| `zkvm/config` | vkey record, program config, input manifest |
| `zkvm/scripts` | Build and helper scripts |
| `zkvm/docs/handoff.md` | Handoff page for running the GPU proving |

`zkvm/` depends on `rust-nostd-verifier/fp-core` by a relative path, so the two directories must
stay siblings exactly as they are here.

## Configuration, not constants

The tools take no program-specific constants. The ELF path, the vkey record and the input paths
come from the config file (`zkvm/config/flashprove.json`), so a program change means regenerating
the vkey record and switching the config, with no code change.

## Proof backends

`zkvm/host-exec` drives SP1's native prover and exposes both modes: CPU and GPU (the native
`cpu()` / `cuda()` backends), with GPU as the default. No real proving is run in this repository;
the proving itself is expected to run where a GPU cluster is available.

## Checking and building

See `zkvm/docs/handoff.md` for the frozen artifact hashes, the input convention, and the exact
build, vkey and proving commands. The handoff page also lists the resource estimates.

## License

Apache-2.0. See `LICENSE`, `NOTICE` and `THIRD_PARTY.md`.
