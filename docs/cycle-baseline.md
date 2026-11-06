# Baseline cycle report: SP1 guest execution and cycle measurements

baseline run runs the end-to-end verifier inside an SP1 guest and measures what one execution costs. The guest reuses
`fp-core` read-only: the three stages run through `fp_core::verifier::run_stage`, and a small
assembly in the guest produces the same `result-v1` line and `YES` that `fp-host` prints. The host
calls SP1's execute API only (no proving) and compares the guest's public output with `fp-host`
line by line.

## 1. Toolchain

| Piece | Version | How it was installed |
|---|---|---|
| `cargo prove` (`sp1-cli` package) | **6.10.0** | `cargo install sp1-cli --version 6.10.0 --locked` |
| SP1 zkVM toolchain (`succinct`) | rustc **1.96.0-dev** | `cargo prove install-toolchain` |
| zkVM targets shipped | `riscv64im-succinct-zkvm-elf`, `riscv32im-succinct-zkvm-elf` | in `~/.sp1/toolchains/<id>/lib/rustlib/` |
| Host Rust | rustc 1.97.1 | the repository's toolchain |
| `sp1-zkvm`, `sp1-sdk`, `sp1-core-executor` | pinned `=6.10.0` | `zkvm-prover/guest/Cargo.toml`, `zkvm-prover/host-exec/Cargo.toml` |

`cargo prove --version` prints `cargo-prove sp1 (VERGEN_IDEMPOTENT_OUTPUT 2026-11-05T07:35:46Z)`;
the version is the crates.io package `sp1-cli 6.10.0`, which is the crate that ships the
`cargo-prove` binary (`cargo install cargo-prove` names no crates.io package).

The 6.10.0 toolchain ships both zkVM targets. `cargo prove build` selects
`riscv64im-succinct-zkvm-elf` (`sp1-build`'s `DEFAULT_TARGET`), and the 6.10.0 executor expects that
target; the baseline run task book's `riscv32im-succinct-zkvm-elf` is also installed but is not the one this
toolchain builds by default. This report records the target that was actually used.

## 2. The guest and the host

- `zkvm-prover/guest/` (`#![no_std]`): reads the private input with `sp1_zkvm::io::read` (each byte string
  is length-prefixed: `Vec<u8>`), runs the three stages and commits the call's accounting, its
  `result-v1` line and `YES` (or the rejection) as public output.
- `zkvm-prover/host-exec/` (std): reads the fixtures, writes the same input with `SP1Stdin::write`,
  executes the ELF with `ProverClient::builder().cpu().build()` and `.execute(..).run()`, prints
  the execution report, and compares `result-v1` and `YES` with `fp-host`'s.

The private input is the reference call's five paths flattened: `policy.txt`, `layout.txt`,
`KL.bin` (the configuration folder), `key.bin` and the leaf file that the proof names (the ivk
folder), the request, y and proof files, then the leaf number and the commitment ID.

## 3. Results

One execution of the accepted example with `host-exec` (SP1 6.10.0, circuit v6.1.0, CPU executor,
no proving):

| Figure | Value |
|---|---|
| guest ELF | 3,207,568 bytes (`riscv64im-succinct-zkvm-elf`, not stripped) |
| guest exit code / call status | 0 / 0 |
| **total cycles** | **32,385,267,062** (3.24e10) |
| shards | **1,931** (estimate: `ceil(cycles / shard_size)`, `shard_size` 16,777,216) |
| syscalls | 0 reported by the 6.10.0 execute report in this path (the ECALLs are inside the 32.4G opcode count) |
| memory | `touched_memory_addresses` 0 (not populated in this path); execution-record estimate 9,586,039,050,352 bytes; the zkVM's configured ceiling is `MAX_MEMORY` 137,438,953,472 bytes (128 GiB), input region 17,179,869,184 bytes (16 GiB) |
| execution time | 4,672.21 s (77 min 52 s) in the debug-built CPU executor; the process used about 332% CPU and 17,621 s of user time |

The host-exec output, verbatim:

```
host-exec: sp1 circuit v6.1.0, guest ELF the FlashProve tree/zkvm/target/elf-compilation/riscv64im-succinct-zkvm-elf/release/guest (3207568 bytes)
host-exec: execute 4672.21 s, guest exit code 0, status 0
host-exec: total cycles 32385267062
host-exec: shards 1931 (estimate ceil(cycles / shard_size), shard_size 16777216; the executor also splits at the trace-area thresholds)
host-exec: syscalls 0
host-exec: memory 0 addresses touched, 9586039050352 bytes of execution record
host-exec: public output (6571 bytes):
...
host-exec: result-v1 IDENTICAL
host-exec: YES IDENTICAL
host-exec: PASS (result-v1 and YES are byte-identical to fp-host)
```

The public output is the call's full accounting (the same text `fp-host` prints after
`---- the call ----`), the `result-v1` line and `YES`. It is 6,571 bytes. `result-v1` and `YES`
are byte-identical to `fp-host` run on the same fixtures with `-id` and `-q`; this is the baseline run
consistency gate.

The shard figure is an estimate. The 6.10.0 execute report does not expose the executor's shard
boundaries; it splits on trace-area thresholds (`ELEMENT_THRESHOLD` 2^28 + 2^27 elements,
`HEIGHT_THRESHOLD` 2^22 rows), not on a fixed cycle count. The estimate divides the instruction
count by the configured `shard_size` (2^24) and is an upper bound of the same order; the number
that matters for proving is the prover's own shard count.

## 4. Pitfalls and countermeasures

- **`cargo install cargo-prove` names no crates.io package.** The `cargo prove` binary is shipped
  by the `sp1-cli` package: `cargo install sp1-cli --version 6.10.0 --locked` installs it. The
  version is pinned in the report and the manifests.
- **`rustup target list --installed | grep succinct` is empty.** The SP1 toolchain is a rustup
  *toolchain* named `succinct` (rustc 1.96.0-dev), not a target of the default toolchain. Verify
  with `rustup toolchain list`, and the shipped targets in
  `~/.sp1/toolchains/<id>/lib/rustlib/`.
- **The zkVM target is `riscv64im`, not `riscv32im`, under SP1 6.10.0.** Both targets ship, but
  `sp1-build`'s `DEFAULT_TARGET` and the 6.10.0 executor expect `riscv64im-succinct-zkvm-elf`;
  `cargo prove build` selects it. The document records the target actually used.
- **A `no_std` guest must not define `#[panic_handler]` here.** `sp1-lib` depends on `std`, which
  already provides the panic handler even when the guest crate is `#![no_std]`; a local handler is
  a duplicate lang item (E0152). The guest defines none, and a panic still halts with status 1.
- **The private input is the call's five paths flattened.** A guest cannot read a folder, so the
  configuration folder's three files and the ivk folder's two files are each their own
  length-prefixed input; the guest reads ten values (with the leaf number and the ID).
- **The first execution is expensive.** 32.4G cycles took 78 minutes in the debug-built CPU
  executor; a release host-exec and the prover's GPU shards are faster, but the cycle count is the
  instruction count and does not change. The call's accounting and `result-v1` are identical, so
  the cost is the verifier itself, not an artifact of the guest assembly.
- **The 6.10.0 execute report leaves the syscall and memory counters empty.** Only
  `opcode_counts` (hence `total_instruction_count`) is populated in this path; the report prints
  the zeros and the toolchain's memory configuration rather than inventing a usage figure.
