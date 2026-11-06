#!/usr/bin/env bash
# The gates that do not need a GPU: schemas, tools, contracts, and (with S6_FULL=1) the SP1
# execution gate against fp-host.
#
#   ./zkvm-prover/scripts/s6-check.sh              # builds + unit tests + gen-vkey --check + forge test
#   S6_FULL=1 ./zkvm-prover/scripts/s6-check.sh    # also executes the accepted example (several minutes)
#
# Set CONFIG to test another configuration file (default config/flashprove.json).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CONFIG="${CONFIG:-$ROOT/config/flashprove.json}"
ZKVM="$ROOT/zkvm-prover"

echo "== fp-pv and fp-hostlib unit tests =="
cargo test --manifest-path "$ZKVM/Cargo.toml" -p fp-pv -p fp-hostlib

echo "== build the tools and the release host-exec =="
cargo build --release --manifest-path "$ZKVM/Cargo.toml" -p fp-hostlib --bins
cargo build --release --manifest-path "$ZKVM/Cargo.toml" -p host-exec

echo "== the vkey record must match the ELF on disk (hash only; --check re-derives the vkey) =="
"$ZKVM/target/release/gen-vkey" --root "$ROOT" --config "$CONFIG" --check-elf

echo "== contracts =="
(cd "$ZKVM/contracts" && forge test)

if [ "${S6_FULL:-0}" = "1" ]; then
  echo "== execute the accepted example and compare with fp-host =="
  cargo build --manifest-path "$ROOT/rust-verifier/Cargo.toml" -p fp-host
  "$ZKVM/target/release/host-exec" --root "$ROOT" --config "$CONFIG"
else
  echo "(set S6_FULL=1 to run the SP1 execution gate against fp-host)"
fi
