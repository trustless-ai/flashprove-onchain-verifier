# End-to-end CPU Groth16 proof and local on-chain verification

**Status: completed.** On 2026-11-26/27, the accepted FlashProve example was proved end to end
with SP1 6.10.0 and circuit v6.1.0 in **CPU Groth16** mode, and the resulting bundle was verified
on a local Anvil chain by the official `sp1-contracts` v6.1.0 verifier, `FlashProveZKVerifier`,
and `ExampleAgentVerifier`. The proof was accepted (`verdict=YES`, `call_status=0`), the valid call
emitted `valid=true`, and `usedTasks` changed to `true`. Tampered proof, tampered public values and
a repeated task were all rejected.

This report is a record of that run and a reproduction guide. It does not claim that a rebuild
always produces the same guest ELF bytes; the approved ELF and its vkey are identified below. All
on-chain work was local; no testnet or mainnet deployment was made. No proof was re-run while
writing this report.

**Source availability.** This report, `docs/scripts/verify-onchain-local.sh` and
`docs/scripts/bundle-tools.py` are added by the public PR branch
`docs/cpu-groth16-end-to-end` on the JimmyShi22 fork; fetch them from that branch. The branch is a
review branch and may change until its PR is merged; after merge, use the merged commit. The base
source commit `01a7167` does not contain them. This page does not claim that the branch is merged
or released, and the approved ELF is still not publicly available.

## 1. Result at a glance

| Item | Recorded value |
|---|---|
| Proof system | SP1 6.10.0, circuit v6.1.0, Groth16 |
| Backend | CPU (`--mode cpu --proof-mode groth16`) |
| Verdict / call status | `YES` / `0` |
| Commitment ID | `0x79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183` |
| Input digest | `0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392` |
| Output hash | `0x0af488bb91e0d3b3b645a7f44f990968e50312a40ff4c88b0d606283e9b4ec43` |
| `proof.bytes` / public values / bundle | 356 B / 6,711 B / 7,232 B |
| Proof command window | 2026-11-26T14:33:32Z to 2026-11-27T22:33:53Z |
| Internal `proof_seconds` | 115,206.248 s (32 h 0 min 6.248 s) |
| Local chain result | valid bundle accepted, `usedTasks=true`; tamper and repeat rejected |

The command window includes about 15 s of setup/startup outside the reported `proof_seconds`; the
two figures describe different intervals and are not added together.

## 2. Identity: source, ELF, vkey, inputs

### 2.1 Source

- Repository: the public `flashprove-onchain-verifier` fork of the `trustless-ai` project.
- Base commit: `01a7167536cad26fc0042d393cb7e674daf314c5`
  (`fix(host): pack the guest stage selector into stdin exactly once`).
- The run used a clean `git archive` copy of that commit; the working tree had no source changes
  other than the configuration/vkey updates described in §4.

### 2.2 Approved guest identity

| Field | Value |
|---|---|
| Guest ELF size | **12,242,912 bytes** |
| Guest ELF SHA-256 | **`f31e45a8e29cb63182045517291262422cf86692f02d1989ab7b04d1b74b860b`** |
| Program vkey (`bytes32`) | **`0x00077170f863a7960a725e58df8b8f3d111e58468d7d987618983ce1dc1a8f00`** |
| SP1 SDK / circuit | 6.10.0 / v6.1.0 |
| Input digest | `0xe0ea24c85e2fe7e6458b8d574aa429bb0e9e7ce0a25b6efc605e4afbd3294392` |
| Guest cycles | 27,547,235,173 (measured by `host-exec`) |

The approved ELF is the artifact produced by the isolated Docker guest build described in §4.
The identity that every proof, public value, metadata field and on-chain wrapper in this run uses
is the triple above: ELF SHA-256, vkey, and input digest.

### 2.3 Historical baseline (not used by this run)

An earlier record in `config/vkey.json` described a different guest:

| Field | Historical value |
|---|---|
| ELF size | 12,245,688 bytes |
| ELF SHA-256 | `2d077855ff441449f6778a432d8cca59ff65922b1c48a766dc2ed9bca070f652` |
| Program vkey | `0x00200f72646a715059f034051e4624c3f6940a6d2c2c4dca8aa3575c45f29464` |

That record was superseded before the run. Its original ELF is **not present on the machine that
produced this run**; the machine preserves the old record and an old failed local ELF
(12,245,488 bytes, SHA-256 `462ae622bbec5671ed2e80d533cafb9e364e692cff0da6be58f9ebe35da0182f`)
as history. Nothing in the accepted proof or the on-chain closure binds the old vkey. Do not mix
the two identities: a Groth16 proof is tied to one ELF and one vkey, and the wrapper binds the vkey
through `metadata`.

### 2.4 How the approved ELF was obtained

The ELF was built with the official SP1 Docker path, not by a host-native build:

```sh
(
cd "$ROOT/zkvm-prover"
cargo prove build --docker --locked \
  --workspace-directory "$ROOT" \
  -p guest --binaries guest \
  --rustflags="-Cllvm-args=-inline-threshold=1000"
)
cd "$ROOT"
```

Observed build environment for the approved artifact:

| Item | Value |
|---|---|
| Image | `ghcr.io/succinctlabs/sp1:v6.10.0` |
| OCI index digest | `sha256:9363a70004271de441e863612c7aefbbc5c36f371f111cd8abb1672fa5ea99f1` |
| linux/amd64 manifest | `sha256:d731d3c40e4e74f606b5203d2d54fca4ee398b00a023d23cc6a6506709af4905` |
| Guest rustc | 1.96.0-dev (SP1 toolchain inside the Docker image) |
| Guest cargo | stable fallback 1.99.1 |
| Host rustc / cargo | 1.100.0 (`0ef1bc386` / `3acc79c0c`) |
| `sp1-cli` | 6.10.0 |
| Build result | ELF 12,242,912 B, SHA-256 `f31e45a8…b860b` |

The two lock files were unchanged across the build:

- `zkvm-prover/Cargo.lock`: `651fbc8e7a42283da434d34f4b89c5ad3a854058e762f27b366e6f97e42d62eb`
- `rust-verifier/Cargo.lock`: `67614726c1c1efbf59b7bba3b5855e1f115044a01c575d95410f684cde237252`

**Reproducibility boundary.** The command and image above are the provenance of the approved
artifact. This report does **not** claim that rebuilding the same source always yields the same
ELF bytes. Compiler/toolchain versions, build paths, link order and other environment details can
change the bytes, and the historical record above is an example of a different build result. Use
the approved ELF when reproducing this exact proof. If a rebuild produces a different hash, treat
it as a new program identity: run `gen-vkey --update`, redeploy or reconfigure the wrapper with the
new vkey, and produce a new proof. The checked-in `config/vkey.json` at the base commit still
contains the historical record; the run updated it locally as described in §4.

## 3. Requirements

The recorded run used a Linux x86-64 machine with 64 vCPUs, a nominal **512 GiB** of RAM
(the OS reports **495 GiB usable**: `MemTotal=519,390,536 KiB`), a 2 TiB disk, and no GPU; CPU
Groth16 does not use CUDA. A host with less memory or disk can run the small-input stages but may
not fit the accepted proof's shard workers. The following tools must be available:

- Rust host toolchain 1.100.0 and Cargo;
- `sp1-cli` 6.10.0 (`cargo install sp1-cli --version 6.10.0 --locked`);
- the SP1 `succinct` toolchain used by the guest build (the Docker image supplies the guest rustc);
- Docker, for the SP1 guest build and the gnark Groth16 wrap step;
- SP1 circuit artifacts for v6.1.0 (the Groth16 circuit archive; the run used a pre-installed
  `SP1_GROTH16_CIRCUIT_PATH`);
- Foundry 1.10.0 (`forge`, `cast`, `anvil`);
- `solc` 0.8.20 for the official `sp1-contracts` v6.1.0 verifier artifact (the wrapper contracts
  use the repository's `foundry.toml`, which pins solc 0.8.24).

### 3.1 System packages, toolchain and circuit artifacts

The recorded host was Alibaba Cloud Linux 4. The package set installed for the run included
`clang`, `clang-devel`, `cmake`, `gcc-c++`, `git`, `jq`, `openssl-devel`, `protobuf-compiler`,
`protobuf-devel`, `unzip`, `docker`, `docker-client`, `containerd`, `htop`, `lsof`, `bzip2`.
The exact package versions are in the private evidence archive; an equivalent Linux x86-64
package set is acceptable if the commands below pass. Do not install from unverified mirrors.

```sh
# example package installation on the recorded distribution
sudo dnf install -y clang clang-devel cmake gcc-c++ git jq openssl-devel   protobuf-compiler protobuf-devel unzip docker docker-client containerd htop lsof bzip2
sudo systemctl enable --now docker

# Rust host toolchain (the run used 1.100.0; 1.97.1 was installed as a parity reference)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
. "$HOME/.cargo/env"
rustup toolchain install 1.100.0 --profile minimal
rustup default 1.100.0
rustup toolchain install 1.97.1 --profile minimal

# SP1 CLI and guest toolchain
cargo install sp1-cli --version 6.10.0 --locked
cargo prove --version
# The Docker guest build supplies its own rustc 1.96.0-dev. The host `succinct` toolchain was
# also present; verify it if you use a host build path.
rustup toolchain list
```

The guest build and Groth16 wrap use these two images:

```sh
docker pull ghcr.io/succinctlabs/sp1:v6.10.0
docker pull ghcr.io/succinctlabs/sp1-gnark:v6.1.0
docker image inspect ghcr.io/succinctlabs/sp1:v6.10.0 --format '{{.Id}}'
docker image inspect ghcr.io/succinctlabs/sp1-gnark:v6.1.0 --format '{{json .RepoDigests}}'
```

The recorded image IDs/digests are in §2.4 and §7; an image with a different digest is a different
build environment and must be recorded as such.

The Groth16 circuit archive is a third-party download, not part of this repository:

```sh
export WORK="${WORK:-$PWD/fpov-work}"
export SP1_GROTH16_CIRCUIT_PATH="$WORK/.sp1/circuits/groth16"
export SP1_CIRCUIT_MODE=release
(
set -euo pipefail
mkdir -p "$WORK" "$SP1_GROTH16_CIRCUIT_PATH"
CIRCUIT_DIR="$SP1_GROTH16_CIRCUIT_PATH/v6.1.0"
ARCHIVE="$WORK/v6.1.0-groth16.tar.gz"
STAGE="$SP1_GROTH16_CIRCUIT_PATH/.v6.1.0.incomplete.$$"
OLD="$CIRCUIT_DIR.old.$$"
cleanup() {
  rm -rf "$STAGE"
  # If the old valid directory was moved aside but the new directory never appeared,
  # restore it even when the shell exits on an interrupt.
  if [ ! -e "$CIRCUIT_DIR" ] && [ -e "$OLD" ]; then mv "$OLD" "$CIRCUIT_DIR"; fi
}
trap cleanup EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
[ ! -e "$OLD" ] || { echo "refusing: backup already exists: $OLD"; exit 1; }
curl -L --retry 5 --retry-delay 5 \
  https://sp1-circuits.s3-us-east-2.amazonaws.com/v6.1.0-groth16.tar.gz \
  -o "$ARCHIVE"
test "$(stat -c%s "$ARCHIVE")" = "6211807514"
test "$(sha256sum "$ARCHIVE" | awk '{print $1}')" = \
  "18beebb6cd0cc9b4d4a240ee4f49511da6c2a7e51724bad4232de538a9147810"
tar -tzf "$ARCHIVE" >/dev/null
gzip -t "$ARCHIVE"
# The archive's top level is `./`; SP1's build.rs reads base.join("v6.1.0").
# Extract into a staging directory; never delete a valid cache before the new one passes checks.
rm -rf "$STAGE"
mkdir -p "$STAGE"
tar -xzf "$ARCHIVE" -C "$STAGE"
check() { test "$(stat -c%s "$STAGE/$1")" = "$2"; }
# The seven formal files in the archive (Apple `._` resource forks are ignored).
check groth16_vk.bin 492
check groth16_pk.bin 5862173061
check groth16_circuit.bin 2437991441
check groth16_witness.json 2802920
check constraints.json 111997113
check Groth16Verifier.sol 26770
check SP1VerifierGroth16.sol 3236
touch "$STAGE/.complete"
if [ -e "$CIRCUIT_DIR" ]; then mv "$CIRCUIT_DIR" "$OLD"; fi
if mv "$STAGE" "$CIRCUIT_DIR"; then
  rm -rf "$OLD"
else
  [ -e "$OLD" ] && mv "$OLD" "$CIRCUIT_DIR"
  exit 1
fi
trap - EXIT
)
```

The recorded run used a pinned prebuilt Foundry 1.10.0. Install that exact official release and
load it into the current shell:

```sh
export FOUNDRY_VERSION=1.10.0
export FOUNDRY_DIR="${FOUNDRY_DIR:-$HOME/.foundry}"
FOUNDRY_TARBALL="$PWD/foundry_v${FOUNDRY_VERSION}_linux_amd64.tar.gz"
(
set -euo pipefail
curl -fL --retry 5 \
  "https://github.com/foundry-rs/foundry/releases/download/v${FOUNDRY_VERSION}/foundry_v${FOUNDRY_VERSION}_linux_amd64.tar.gz" \
  -o "$FOUNDRY_TARBALL"
echo "90729233bd9a683b872783ae2e3217fb56876fa2a3c37185f13e39dca8525041  $FOUNDRY_TARBALL" | sha256sum -c -
mkdir -p "$FOUNDRY_DIR/bin"
tar -xzf "$FOUNDRY_TARBALL" -C "$FOUNDRY_DIR/bin"
)
export PATH="$FOUNDRY_DIR/bin:$PATH"
forge --version | head -1     # must show Version: 1.10.0
cast --version | head -1
anvil --version | head -1
```

The archive SHA-256 above is the official 1.10.0 Linux amd64 asset. Do not let a generic
`foundryup` silently replace this with a newer version; if you install another version, record it
and treat it as a different toolchain. The recorded environment used 1.10.0 for the official
verifier build and Anvil calls.

The official verifier's `foundry.toml` pins solc 0.8.20; the repository wrapper config pins
0.8.24. Install/select the compiler used by the relevant build rather than reusing an artifact
from a different compiler.

Preflight checks before building:

```sh
docker info >/dev/null
docker run --rm ghcr.io/succinctlabs/sp1:v6.10.0 rustc +succinct --version
df -h /                      # observed free space was ~1.8 TiB during the run; this is NOT a minimum requirement
free -g                      # the accepted proof peak was ~227 GiB whole-machine use
cargo prove --version
forge --version
anvil --version
test -n "$SP1_GROTH16_CIRCUIT_PATH"
test -f "$SP1_GROTH16_CIRCUIT_PATH/v6.1.0/groth16_vk.bin"   # archive layout check
```
passed **both** explicit flags:

```sh
--mode cpu --proof-mode groth16
```

Omitting `--mode cpu` on a CUDA-default configuration selects the CUDA path; omitting
`--proof-mode groth16` can select an off-chain proof type. Neither is what produced this record.

## 4. Build and configure

Set the workspace variables first; every later command uses these names:

```sh
export WORK="$PWD/fpov-work"
export ROOT="$WORK/flashprove-onchain-verifier"
export OUT="$WORK/run-output"
export ELF="$ROOT/zkvm-prover/target/elf-compilation/docker/riscv64im-succinct-zkvm-elf/release/guest"
export SP1_CONTRACTS="$WORK/sp1-contracts-v6.1.0"
export SP1_GROTH16_CIRCUIT_PATH="${SP1_GROTH16_CIRCUIT_PATH:-$WORK/.sp1/circuits/groth16}"
export SP1_CIRCUIT_MODE=release
export FOUNDRY_DIR="${FOUNDRY_DIR:-$HOME/.foundry}"
export PATH="$FOUNDRY_DIR/bin:$PATH"
export RPC="http://127.0.0.1:8545"
export DEPLOYER_PRIVATE_KEY="..."   # set in your shell to a disposable key; never commit it
mkdir -p "$WORK" "$OUT"
# WARNING: the verifier scripts write $OUT/onchain. Use a fresh dedicated OUT,
# or deliberately accept that a later stage overwrites the earlier stack/summary.
# There is no automatic protection against overwriting existing evidence.

git clone https://github.com/JimmyShi22/flashprove-onchain-verifier.git "$ROOT"
cd "$ROOT"
git checkout 01a7167536cad26fc0042d393cb7e674daf314c5

git clone https://github.com/succinctlabs/sp1-contracts.git "$SP1_CONTRACTS"
git -C "$SP1_CONTRACTS" checkout 2ac5ecbbe473421a963d67e55f182e9a36576f7c

cargo build --release -p fp-hostlib --bins --manifest-path zkvm-prover/Cargo.toml
cargo build --release -p host-exec --manifest-path zkvm-prover/Cargo.toml
cargo build -p fp-host --manifest-path rust-verifier/Cargo.toml
```

**Environment isolation.** Use a fresh shell and dedicated `CARGO_HOME`, `RUSTUP_HOME` and
`TMPDIR`; do not inherit `RUSTFLAGS`, `RUSTC_BOOTSTRAP`, `CARGO_TARGET_DIR`, `RUSTUP_TOOLCHAIN`,
`SP1_DOCKER_IMAGE` or another project's `.cargo/config.toml`. The recorded Docker build explicitly
had `SP1_DOCKER_IMAGE` unset. If a cargo mirror config is required, record its bytes/hash; do not
let a stale global config silently change the dependency source.

Build the guest with §2.4. The base commit's `config/vkey.json` records the **historical** ELF,
and its `config/flashprove.json` and `config/flashprove.smoke.json` point at the host build path.
The recorded run changed the `program.elf` line in **both** configuration files to the Docker
output path, and regenerated the vkey record:

```text
"elf": "zkvm-prover/target/elf-compilation/docker/riscv64im-succinct-zkvm-elf/release/guest"
```

The main configuration keeps `prover.mode = "cuda"`; the smoke configuration keeps
`prover.mode = "cpu"`; both keep `proof_mode = "groth16"`. No other configuration edit was made.
The recorded final hashes were: `config/flashprove.json` `33a5b474…379a`,
`config/flashprove.smoke.json` `54a17bf8…7ee4`, `config/vkey.json` `3feb406e…b080`.
A user who edits formatting may get different file hashes; the identity fields are what matter.

**Check the ELF before `gen-vkey`.** The approved ELF is not yet published from this repository;
its public release/licensing is pending. If a maintainer supplies the artifact, verify it first;
if you rebuild, it is a new artifact unless its bytes match:

```sh
test -f "$ELF" || { echo "approved ELF not available; stop"; exit 1; }
test "$(stat -c%s "$ELF")" = "12242912" || { echo "ELF size differs"; exit 1; }
test "$(sha256sum "$ELF" | awk '{print $1}')" = "f31e45a8e29cb63182045517291262422cf86692f02d1989ab7b04d1b74b860b" \
  || { echo "ELF SHA differs; this is a new identity, not the recorded proof"; exit 1; }
```

If that check fails, do **not** run `gen-vkey --update` and accept whatever vkey appears: that
would silently change the program identity. Stop and obtain the approved artifact, or regenerate
the vkey and treat the run as a new program/identity with a new deployment. Without the approved
ELF, exact reproduction of this proof is blocked.

After the check, point the record at the ELF and regenerate it:

```sh
zkvm-prover/target/release/gen-vkey --root "$ROOT" --config config/flashprove.json --update
zkvm-prover/target/release/gen-vkey --root "$ROOT" --config config/flashprove.json --check-elf
zkvm-prover/target/release/gen-vkey --root "$ROOT" --config config/flashprove.json --check
```

The `--update` command performs the ELF-to-vkey setup; the recorded run took about 12.7 s for that
setup on the host. `--check-elf` is the fast hash-only check and must print `MATCH`; `--check`
re-derives the vkey and must also print `MATCH`.

Before proving, check the accepted input manifest and validate the plan:

```sh
zkvm-prover/target/release/fp-pv manifest --root "$ROOT" \
  --config config/flashprove.json --check config/input-manifest.json

zkvm-prover/target/release/fp-prover prove --root "$ROOT" \
  --config config/flashprove.json --plan --mode cpu --proof-mode groth16
```

The manifest check must print `MATCH (9 files, leaf 0, input digest 0xe0ea24c8…3294392)`; the plan
must print the approved ELF/vkey and `PLAN ONLY`, and must not create an output directory.

## 5. The six stages

Run every stage with the current directory set to `$ROOT`; the commands below use repository-
relative paths (`config/...`, `rust-verifier/...`, `docs/scripts/...`). The Stage 4 subshell
changes only its PORT/RPC/STACK_ONLY environment, not the cwd. The run proceeded in gates; each
gate kept its own output, and a failed earlier gate was not used as evidence for a later one.

### Stage 1 — environment and frozen identity

The machine was inventoried (OS, CPU, memory, disk, no NVIDIA device), the toolchain and Docker
paths were installed, and the source was frozen at `01a7167`. The accepted manifest and the
production plan were checked as in §4. This stage establishes the identity, not a proof.

Recorded results: manifest `rc=0`, plan `rc=0`, ELF `f31e45a8…`, vkey `0x00077170…`, SDK 6.10.0,
circuit v6.1.0, mode `cpu`, proof mode `groth16`, `PLAN ONLY`.

### Stage 2 — small-input mock and `fp-pv` comparison

The smoke configuration uses synthetic zero inputs and, in the recorded run, its `program.elf`
line was also changed to the Docker output (see §4); it still uses `prover.mode=cpu` and
`proof_mode=groth16`. It exercises configuration loading, vkey check, stdin packing, setup, guest
execution, mock proof, local verification, `pv.bin` and bundle writing, but it is **not a proof**:

```sh
zkvm-prover/target/release/fp-prover prove --root "$ROOT" \
  --config config/flashprove.smoke.json --mock --mode cpu \
  --out "$OUT/smoke-mock"

rust-verifier/target/debug/fp-host \
  zkvm-prover/fixtures/smoke/config zkvm-prover/fixtures/smoke/ivk \
  zkvm-prover/fixtures/smoke/example.req zkvm-prover/fixtures/smoke/example.y \
  zkvm-prover/fixtures/smoke/example.proof \
  -id 0000000000000000000000000000000000000000000000000000000000000000 -q \
  > "$OUT/fp-host-smoke.out"

zkvm-prover/target/release/fp-pv expected --root "$ROOT" \
  --config config/flashprove.smoke.json --fp-host-output "$OUT/fp-host-smoke.out" --json
zkvm-prover/target/release/fp-pv decode --file "$OUT/smoke-mock/pv.bin" --json
zkvm-prover/target/release/fp-pv check --root "$ROOT" \
  --config config/flashprove.smoke.json --fp-host-output "$OUT/fp-host-smoke.out" \
  --pv-file "$OUT/smoke-mock/pv.bin"
```

Recorded result: `rc=0`, wall 3.6 s (setup 2.3 s, mock proof 0.8 s), proof bytes 0. The
smoke public values are intentionally not an acceptance: `verdict=NO`, `call_status=1`,
`result_v1_status=0`, commitment `0x0`, output hash `0x0`. `fp-host` prints `NO: KL-length` and
exits 1; that is the expected negative/zero-input semantics, not a pipeline failure. The smoke
input digest `0xab853a00…` was identical in the mock output, `fp-pv expected`, `pv.bin` and `check`.

### Stage 3 — placeholder Anvil path

This stage verifies the ERC-8274 call path with a **placeholder proof** and
`MockSP1Verifier`. It is not a real proof and not a real SP1 verifier:
It must not be cited as cryptographic evidence.

```sh
ANVIL_PORT=8548 contracts/scripts/anvil-smoke.sh
```

The script reads the vkey, commitment ID, accepted-verdict mask (`6`), status rule and agent from
the configuration, computes the real `FPV1` block, and walks the wrapper path with a placeholder
string. Recorded result: five local transactions status `0x1`; the event has `valid=true`; the
script exits 0. The contract addresses and receipt are local-run artifacts; they do not carry over
to another chain. The placeholder is accepted only by the mock verifier.

### Stage 4 — small-input real CPU Groth16 plus the real verifier

This stage uses the real SP1 verifier with a real Groth16 proof over synthetic smoke inputs. It
demonstrates that the proof format, the verifier and the wrapper stack work, while correctly
rejecting the smoke call at the business layer because the smoke public values are not the
accepted call.

Proof:

```sh
zkvm-prover/target/release/fp-prover prove --root "$ROOT" \
  --config config/flashprove.smoke.json \
  --mode cpu --proof-mode groth16 \
  --out "$OUT/small-groth16"
```

Recorded result: `rc=0`; setup 2.3 s; proving 150.9 s; `proof.bytes` 356 B; SDK local
verification passed; `verdict=NO`, `call_status=1`, input hash `0xab853a00…`. The proof is real,
but the call is a smoke call; it is not an acceptance.

The official `sp1-contracts` v6.1.0 `SP1Verifier` (Groth16; solc 0.8.20) was deployed locally and
called directly. Deploy the same stack used by Stage 6, but stop after deployment and keep Anvil
alive for these calls:

```sh
(
export PORT=8549 RPC=http://127.0.0.1:8549 KEEP_ANVIL=1 STACK_ONLY=1
export BUNDLE="$OUT/small-groth16/bundle.bin"
export SUMMARY="$OUT/small-groth16/summary.json"
docs/scripts/verify-onchain-local.sh

SP1_VERIFIER=$(jq -r '.official' "$OUT/onchain/stack.json")
ZK_VERIFIER=$(jq -r '.zk' "$OUT/onchain/stack.json")
AGENT_VERIFIER=$(jq -r '.agent' "$OUT/onchain/stack.json")
VKEY=$(jq -r '.vkey' "$OUT/onchain/stack.json")
AGENT_ID=$(jq -r '.chain.authorized_agents[0]' "$ROOT/config/flashprove.json")
INPUT_HASH=$(jq -r '.input_digest' "$OUT/small-groth16/summary.json")
OUTPUT_HASH=$(jq -r '.output_hash' "$OUT/small-groth16/summary.json")
PV_HEX="0x$(xxd -p -c 999999 "$OUT/small-groth16/public_values.bin")"
PROOF_HEX="0x$(xxd -p -c 999999 "$OUT/small-groth16/proof.bytes")"
BUNDLE_HEX="0x$(xxd -p -c 999999 "$OUT/small-groth16/bundle.bin")"

cast call "$SP1_VERIFIER" "verifyProof(bytes32,bytes,bytes)" "$VKEY" "$PV_HEX" "$PROOF_HEX" --rpc-url "$RPC"
INNER=$(cast call "$ZK_VERIFIER" "verify(bytes32,bytes32,bytes,bytes)(bool)" \
  "$INPUT_HASH" "$OUTPUT_HASH" "$(cast abi-encode 'f(bytes32)' "$VKEY")" "$BUNDLE_HEX" --rpc-url "$RPC")
test "$INNER" = "true" || { echo "inner verifier did not accept the real small proof"; exit 1; }
cast send "$AGENT_VERIFIER" "verify(bytes32,bytes32,bytes32,bytes32,bytes)" \
  "$(cast keccak 'stage4-small-input')" "$AGENT_ID" "$INPUT_HASH" "$OUTPUT_HASH" "$BUNDLE_HEX" \
  --rpc-url "$RPC" --private-key "$DEPLOYER_PRIVATE_KEY" --json > "$OUT/small-groth16/agent-call.json"
test "$(cast call "$AGENT_VERIFIER" 'usedTasks(bytes32)(bool)' \
  "$(cast keccak 'stage4-small-input')" --rpc-url "$RPC")" = "false" \
  || { echo "business layer consumed the smoke task unexpectedly"; exit 1; }

# real verifier negatives: tamper the public values, and use the historical old vkey
cp "$OUT/small-groth16/public_values.bin" "$OUT/small-groth16/pv-tamper.bin"
python3 - "$OUT/small-groth16/pv-tamper.bin" <<'PY'
import sys
p = sys.argv[1]
b = bytearray(open(p, 'rb').read())
b[-1] ^= 1
open(p, 'wb').write(b)
PY
PV_TAMPER_HEX="0x$(xxd -p -c 999999 "$OUT/small-groth16/pv-tamper.bin")"
if cast call "$SP1_VERIFIER" "verifyProof(bytes32,bytes,bytes)" "$VKEY" "$PV_TAMPER_HEX" "$PROOF_HEX" --rpc-url "$RPC" >/dev/null 2>&1; then
  echo "tampered public values unexpectedly verified"; exit 1
fi
OLD_VKEY=0x00200f72646a715059f034051e4624c3f6940a6d2c2c4dca8aa3575c45f29464
if cast call "$SP1_VERIFIER" "verifyProof(bytes32,bytes,bytes)" "$OLD_VKEY" "$PV_HEX" "$PROOF_HEX" --rpc-url "$RPC" >/dev/null 2>&1; then
  echo "historical vkey unexpectedly verified"; exit 1
fi

kill "$(jq -r '.anvil_pid' "$OUT/onchain/stack.json")" 2>/dev/null || true
)
```

Recorded direct-call result: no revert; the sent transaction had status 1. Tampering the public
values and using the old vkey both reverted with `ProofInvalid`. The inner
`FlashProveZKVerifier` returned `true` for the real proof; the outer `ExampleAgentVerifier`
returned `false` and left `usedTasks=false` because the smoke block's commitment/verdict does not
match the configured accepted call. That is the designed business-layer result, not a verifier
failure.

A fresh replay of this Stage 4 sequence on 2026-11-28 used the **existing** small proof (no proof
regeneration) and saved the independent outputs: direct call rc=0, inner call `true`, business
receipt status `0x1` with event `valid=false`, `usedTasks=false`, and both PV-tamper and old-vkey
calls reverting `ProofInvalid`. This is a verifier replay, not a new proof and not a full
clean-machine execution of every stage.

### Stage 5 — accepted formal proof

The production configuration was used with the approved ELF/vkey and explicit CPU Groth16 flags:

```sh
zkvm-prover/target/release/fp-prover prove --root "$ROOT" \
  --config config/flashprove.json \
  --mode cpu --proof-mode groth16 \
  --out "$OUT/accepted"
```

Recorded result: one run, `rc=0`; `verdict=YES`, `call_status=0`; commitment
`0x79a5a2bc…b22183`; input digest `0xe0ea24c8…3294392`; output hash `0x0af488bb…b4ec43`;
SDK local verification passed. The eight output files are listed in §6. The production
configuration still has `prover.mode = "cuda"`; the CPU flags above override it for this run and
were not written back into the configuration.

Create the accepted `fp-host` output that the comparison consumes (run this from `$ROOT`; the
accepted ID is the 64-hex value in `rust-verifier/fixtures/ID.txt`):

```sh
FP_HOST=rust-verifier/target/debug/fp-host
ACCEPTED_ID=$(tr -d '\n' < rust-verifier/fixtures/ID.txt)
"$FP_HOST" \
  rust-verifier/fixtures/config rust-verifier/fixtures/ivk \
  rust-verifier/fixtures/example.req rust-verifier/fixtures/example.y \
  rust-verifier/fixtures/example.proof -id "$ACCEPTED_ID" -q \
  > "$OUT/accepted-fp-host.out"
```

The command must exit 0 and the file must end with `YES`; `accepted-fp-host.out` is the input to
`fp-pv expected`/`check` below.

Independent `fp-pv` comparison on the same inputs and proof:

```sh
zkvm-prover/target/release/fp-pv manifest --root "$ROOT" \
  --config config/flashprove.json --check config/input-manifest.json
zkvm-prover/target/release/fp-pv expected --root "$ROOT" \
  --config config/flashprove.json --fp-host-output "$OUT/accepted-fp-host.out"
zkvm-prover/target/release/fp-pv decode --file "$OUT/accepted/pv.bin"
zkvm-prover/target/release/fp-pv check --root "$ROOT" \
  --config config/flashprove.json --fp-host-output "$OUT/accepted-fp-host.out" \
  --pv-file "$OUT/accepted/pv.bin"
```

Recorded: manifest `MATCH`; `fp-host` prints `YES` with exit 0; `expected` and `decode` are
byte-identical; `check` prints `MATCH (verdict YES, id 0x79a5…b22183)`. The accepted input digest
was also recomputed independently from the nine manifest files and matched the public value.

### Stage 6 — local on-chain closure

The accepted bundle was sent to a disposable local Anvil chain with the official `sp1-contracts`
v6.1.0 verifier, not the mock. The executable, reviewable steps are in
`docs/scripts/verify-onchain-local.sh`; it was tested with the recorded accepted bundle after this
report draft and does not create a proof.

The script performs the following, in order:

1. builds `$SP1_CONTRACTS/contracts/src/v6.1.0/SP1VerifierGroth16.sol` with the tag's solc 0.8.20
   and uses the artifact at
   `$SP1_CONTRACTS/contracts/out/SP1VerifierGroth16.sol/SP1Verifier.json` (not `SP1_CONTRACTS/out`);
2. starts Anvil on `127.0.0.1:8545`, chain ID 31337, and stops it on exit unless
   `KEEP_ANVIL=1` is set (for the manual checks below);
3. checks the deployed official verifier's `VERSION()`, `VERIFIER_HASH()` and `VK_ROOT()`, then
   deploys `FlashProveZKVerifier` and `ExampleAgentVerifier`, reading the vkey, commitment ID,
   accepted mask, status rule and agent from `config/flashprove.json`;
4. sends the valid accepted bundle, a proof-tampered bundle, a public-values-tampered bundle, and
   a repeat of the valid task;
5. decodes every `VerificationCompleted` event, recomputes `verificationDigest`, and queries
   `usedTasks(taskId)` independently for each distinct task;
6. saves `cast tx` and the full receipt separately, ABI-decodes the actual transaction input, and
   compares the decoded bundle to the tested bundle byte-for-byte;
7. writes receipts, `*.input-check.json` and `*.summary.json` per case and exits nonzero on any
   mismatch.

The script always writes `$OUT/onchain/stack.json` after deployment, including in full mode. A
Stage 4 and Stage 6 run can share the documented `$OUT`: Stage 6 replaces Stage 4's stack/summary
files with its own current addresses/PID. If both stages' artifacts must be preserved separately,
give each stage its own `OUT` (or copy the Stage 4 `onchain/` directory before Stage 6). There is no
automatic overwrite protection.

Run it with the §4 variables and the output of Stage 5:

```sh
# Stage 6 must not inherit Stage 4's STACK_ONLY/PORT/KEEP_ANVIL.
unset STACK_ONLY KEEP_ANVIL
export ROOT=... OUT=... SP1_CONTRACTS=...
export PORT=8545
export RPC="http://127.0.0.1:$PORT"
export DEPLOYER_PRIVATE_KEY=...       # disposable local key; never commit it
export BUNDLE="$OUT/accepted/bundle.bin"
export SUMMARY="$OUT/accepted/summary.json"
docs/scripts/verify-onchain-local.sh
```

The script stops Anvil on exit by default. For the manual `cast` checks below, set
`KEEP_ANVIL=1`; it prints/records the PID and leaves the chain running. Stop it with
`kill "$(jq -r '.anvil_pid' "$OUT/onchain/stack.json")"` when done. If you do not keep it alive,
parse the saved `*.receipt.json` and `*.summary.json` offline instead of issuing live calls.

For an audit trail, the recorded run used Anvil 1.10.0, chain ID 31337, the local RPC only, and
the following matrix:

| Test | Task | Transaction | Event `valid` | `usedTasks` after |
|---|---|---|---|---|
| Tampered proof (`proofBytes[355]`) | `0xaf682cb0…b6cc5` | `0xd49fd474…f997c` | false | false |
| Tampered public values (`publicValues[6710]`) | `0xe70a6869…12d078` | `0x2f7e89a1…79f1ba` | false | false |
| Valid accepted bundle | `0x2523c642…bd730` | `0x90fb7afb…60db75` | **true** | **true** |
| Repeat of the valid task | `0x2523c642…bd730` | `0x7326d9f5…59f207` | false | true (remains true) |

The valid call's calldata decoded to the recorded `bundle.bin`, public values and proof bytes; the
event's input hash, output hash, agent profile and `verificationDigest` were independently
recomputed and matched. All four transactions had receipt status `0x1`; a rejected call emits
`valid=false` rather than reverting. The three negative controls are therefore rejections at the
contract/verifier layer, not absent transactions.

A manual check of the two values that matter after each call. The script writes
`$OUT/onchain/agent-deploy.json` and `$OUT/onchain/valid.summary.json`; set the variables from
those files and the accepted summary:

```sh
AGENT_VERIFIER=$(jq -r '.contractAddress' "$OUT/onchain/agent-deploy.json")
AGENT_ID=$(jq -r '.chain.authorized_agents[0]' "$ROOT/config/flashprove.json")
INPUT_HASH=$(jq -r '.input_digest' "$OUT/accepted/summary.json")
OUTPUT_HASH=$(jq -r '.output_hash' "$OUT/accepted/summary.json")
TASK_ID=$(jq -r '.task' "$OUT/onchain/valid.summary.json")
BUNDLE="$OUT/accepted/bundle.bin"

# independent per-task consumption check
cast call "$AGENT_VERIFIER" 'usedTasks(bytes32)(bool)' "$TASK_ID" --rpc-url "$RPC"

# event digest: decode the data, then recompute the ERC-8274 preimage
TOPIC0=$(cast keccak 'VerificationCompleted(bytes32,bytes32,bytes32,bool,bytes32,bytes32,bytes32,uint256,bytes,bytes)')
DATA=$(jq -r --arg t "$TOPIC0" '.logs[] | select(.topics[0] == $t) | .data' "$OUT/onchain/valid.receipt.json")
DEC=$(cast abi-decode 'f(bool,bytes32,bytes32,bytes32,uint256,bytes,bytes)(bool,bytes32,bytes32,bytes32,uint256,bytes,bytes)' "$DATA")
PREIMAGE=$(cast abi-encode 'f(bytes32,bytes32,bytes32,bytes32,bool,bytes32,uint256,bytes,bytes)' \
  "$TASK_ID" "$AGENT_ID" "$INPUT_HASH" "$OUTPUT_HASH" \
  "$(sed -n '1p' <<<"$DEC")" "$(sed -n '4p' <<<"$DEC")" \
  "$(sed -n '5p' <<<"$DEC" | awk '{print $1}')" \
  "$(sed -n '6p' <<<"$DEC")" "$(sed -n '7p' <<<"$DEC")")
cast keccak "$PREIMAGE"   # must equal topics[3] of the event
```

The wrapper's `verify` function is:

```sh
cast send "$AGENT_VERIFIER" 'verify(bytes32,bytes32,bytes32,bytes32,bytes)' \
  "$TASK_ID" "$AGENT_ID" "$INPUT_HASH" "$OUTPUT_HASH" \
  "0x$(xxd -p -c 999999 "$BUNDLE")" \
  --rpc-url "$RPC" --private-key "$DEPLOYER_PRIVATE_KEY"
```

The script ABI-decodes the 7,232-byte bundle into `publicValues` (6,711 B) and `proofBytes`
(356 B), flips the last byte **inside** the selected field (`proofBytes[355]` or
`publicValues[6710]`), and re-encodes. `docs/scripts/bundle-tools.py` asserts that the target field
changed exactly one byte, the other field is byte-identical, and the re-encoded bundle length is
unchanged; it writes `tamper-proof.fields.json` / `tamper-pv.fields.json` with before/after hashes.
It does not XOR byte 355/6710 of the whole ABI bundle, because those are different locations.
Each negative case gets a new task; the repeat reuses the valid task. The field offsets are
recorded properties of this bundle, not arbitrary offsets for another proof.

The recorded local addresses were:

| Contract | Address |
|---|---|
| Official `SP1Verifier` | `0x5FbDB2315678afecb367f032d93F642f64180aa3` |
| `FlashProveZKVerifier` | `0xe7f1725E7734CE288F8367e1Bb143E90bb3F0512` |
| `ExampleAgentVerifier` | `0x9fE46736679d2D9a65F0992F2272dE9f3c7fa6e0` |

The official verifier artifact SHA-256 was `501cb171…15ebe`; the deployment's creation input and
deployed runtime matched the artifact, and the valid bundle was exact in calldata. These are
deterministic local-run addresses and transactions; they are not a public deployment.

## 6. Artifacts and hashes

Accepted output directory (`out/accepted` in the recorded run):

| File | Size (B) | SHA-256 |
|---|---:|---|
| `proof.bin` | 8,405 | `10464eba34f906fdbd75b5a0d1d3bdb8a8406141f774de5fbb704a35f87027d8` |
| `proof.bytes` | 356 | `f75d969982f1652de7f6763ac7b88e4a02f080bf23f800fcb7d9dde5643c18d7` |
| `public_values.bin` | 6,711 | `1f0bdac6c80e21bece7454bf22459bb1e3e96a1830e6c77bdfa494abd07c12ef` |
| `public_values.hex` | 13,425 | `e6c8db805d7f1c776992242632d5e618ddc7e07c90d6fc59f137a47a3fc6134d` |
| `bundle.bin` | 7,232 | `14c06322317057887f6b464919bae2f8b32b4acdd8869905be61a2320c0ae07a` |
| `bundle.hex` | 14,467 | `e8bafd41b7b4aafd19737ff78ee8c52307d19ba33543aa1d81b10509e3ad22af` |
| `pv.bin` | 128 | `83996c635c7acb17a9b91ff96d4b67ac93b3346dddf50fc91a8a3c8eb4686e4a` |
| `summary.json` | 959 | `89117bcce8cb77d44c8dced522f95ee7127ccf1c06b80ef4b2346b6371c76724` |

On-chain summary and key artifacts:

| Item | SHA-256 |
|---|---|
| On-chain `summary.json` | `38ced174e15db0a2af926d77fd4a434958028376913a18803926fb12fa598b2a` |
| Official verifier artifact | `501cb171d70f4e98decfdca0b8e5f370727107f1f7e6c6dff91ca52df7d15ebe` |
| Valid bundle | `14c06322317057887f6b464919bae2f8b32b4acdd8869905be61a2320c0ae07a` |
| Tampered-proof bundle | `46f4f30f3a56571223f60fd1d0d810b57ab17d77b74b92a712c24603d5c173d0` |
| Tampered-PV bundle | `0517a80308cb238c53a5259969a8cedcd903fc0fc42a41d77c0fc61579fe9a38` |

The full `out/` set has eight files; `proof.bin` is the bincode-serialized
`SP1ProofWithPublicValues`, while `proof.bytes` is the on-chain Groth16 proof and `bundle.bin`
is the exact ABI encoding used in the transaction.

## 7. Measured resources and time

| Phase | Measurement | Caveat |
|---|---|---|
| Accepted proof | 115,206.248 s internal; 32 h 0 min 21 s command window | one run, one machine |
| Accepted proof memory | 226.97 GiB whole-machine used peak (5 s samples); 222.21 GiB process-tree RSS peak | 5 s sampling is not an instantaneous upper bound |
| Accepted proof disk | 1,847 GiB minimum free on `/` (recorded run) | elsewhere measured separately |
| Accepted proof Docker root | 6.7524 GiB peak | local Docker storage |
| Accepted proof inodes | 3,840 independent points, minimum 133,475,280 free | 30 s samples (not 5 s) |
| Accepted proof samples | 22,081 samples; maximum gap 7 s, no gap > 10 s | 5 s sampler; blocked during `du`/`docker stats`; no missing-rate estimate is claimed |
| gnark Groth16 container | about 25 s, seen by `docker ps`; no memory sample | 30 s `docker stats` missed the short container; whole-machine used includes it |
| Small-input Groth16 | 150.9 s proving; 2.3 s setup | separate short run |
| Guest build | 1 m 59 s wall; 7.445 GiB whole-machine peak | sampled window, not a hard bound |
| Approved build disk | 1,856.40 GiB minimum free (corrected) | corrected from raw samples; see the evidence record |

No swap was configured; no OOM event or kernel OOM line was observed. The accepted run's process
cgroup memory limit was `max`; the scope disappeared when the process exited, so the final cgroup
peak was not sampled. These limitations are part of the record, not estimates to be presented as
exact peaks.

## 8. What this proves, and what it does not

- It proves that this accepted example's verifier claim was accepted by the SP1 guest, that the
  resulting Groth16 proof verified through the official v6.1.0 verifier, and that the wrapper
  accepted the exact bundle on a local chain once.
- It does not prove that the input is legitimate, that the weights are hidden, or that the GPU
  CUDA prover follows the same path; this run is CPU-only and uses the accepted synthetic
  fixtures.
- It does not establish a public deployment. All chain activity was a disposable local Anvil
  chain; no testnet or mainnet transaction exists.
- It does not claim byte-for-byte rebuild determinism. The approved ELF is an identified artifact;
  a different build is a different program identity until its vkey is regenerated and bound.
- It does not replace the repository's `docs/handoff.md`: that page retains the historical frozen
  record and its older ELF/vkey. Use this report and the identity in §2 for the completed run.
- The public evidence record is a sanitized index of hashes and receipts. Raw logs and the full
  private archive are not linked from this repository; a sanitized evidence bundle is pending a
  separate publication review. No private URL is used here.

## 9. Reproduction checklist

1. Check out the source commit and build the host tools (§4).
2. Build the guest with the Docker command in §2.4; record the ELF size and SHA-256. Verify
   size `12,242,912` and SHA `f31e45a8…b860b` **before** doing anything with the vkey. If they
   differ, stop: this is a new identity, not the recorded proof.
3. Point both `config/flashprove.json` and `config/flashprove.smoke.json` at the Docker output,
   then run `gen-vkey --update`; require `--check-elf` and `--check` to print `MATCH`.
4. Run `fp-pv manifest --check` and `fp-prover --plan --mode cpu --proof-mode groth16`.
5. Run the smoke mock and compare with `fp-pv` (Stage 2); expect `NO`, not an acceptance.
6. Run the small-input real Groth16 and the real verifier (Stage 4); expect the real verifier to
   accept the proof and the business wrapper to reject the smoke call.
7. Run the accepted CPU Groth16 proof with the approved ELF and inputs (Stage 5); require
   `verdict=YES`, `call_status=0`, and `fp-pv check` `MATCH`.
8. Deploy the official v6.1.0 verifier and the wrapper stack locally (Stage 6); send the valid
   bundle and the three negative controls; require the matrix in §5.
9. Compare the **identity fields** in §2 to §6: ELF size/SHA-256, vkey, input digest, output hash,
   commitment, verdict and call status. These are the fields a new run must reproduce. The
   proof/PV/bundle hashes and `summary.json`'s elapsed time are properties of the recorded run; a
   new proof may differ in bytes and timing. If an identity field differs, stop: you are on a
   different program or input, and the old proof is not evidence for it.
10. If you downloaded a published evidence archive, verify its SHA256SUMS first; that checks the
    integrity of the downloaded originals. It is separate from the identity check for a new run.
