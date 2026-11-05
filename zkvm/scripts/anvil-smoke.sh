#!/usr/bin/env bash
# B3: deploy the ERC-8274 stack to a local anvil and walk the call path with a placeholder proof.
#
# Everything comes from the JSON configuration: the program vkey (or the vkey record), the
# commitment ID, the accepted-verdict mask, the status rule and the authorized agents. The only
# constant is anvil's own first development key, which funds a throwaway local chain.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CONFIG="${CONFIG:-$ROOT/zkvm/config/flashprove.json}"
PORT="${ANVIL_PORT:-8545}"
RPC="http://127.0.0.1:$PORT"
# anvil account #0 (public development key, never for a real chain).
ANVIL_KEY="${ANVIL_KEY:-0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80}"
# The placeholder proof starts with "FP-P"; MockSP1Verifier accepts exactly this shape.
PLACEHOLDER_HEX="${PLACEHOLDER_HEX:-46502d504c414345484f4c4445522d50524f4f46}"

for tool in jq forge cast anvil cargo; do
  command -v "$tool" >/dev/null 2>&1 || { echo "anvil-smoke: missing $tool" >&2; exit 1; }
done

echo "== build the tools and the fp-host reference =="
# Debug builds are enough for a local deployment; the GPU machine builds release.
cargo build -p fp-hostlib --bins --manifest-path "$ROOT/zkvm/Cargo.toml" >/dev/null
cargo build --manifest-path "$ROOT/rust-nostd-verifier/Cargo.toml" -p fp-host >/dev/null

FP_PV="$ROOT/zkvm/target/debug/fp-pv"

echo "== read the deployment parameters from $CONFIG =="
PROGRAM_VKEY="$(jq -r '.chain.program_vkey // empty' "$CONFIG")"
if [ -z "$PROGRAM_VKEY" ]; then
  RECORD="$(jq -r '.program.vkey_record' "$CONFIG")"
  PROGRAM_VKEY="$(jq -r '.sp1.vkey_bytes32' "$ROOT/$RECORD")"
fi
COMMITMENT_ID="$(jq -r '.chain.commitment_id' "$CONFIG")"
REQUIRE_STATUS_ZERO="$(jq -r '.chain.require_status_zero' "$CONFIG")"
AGENT_ID="$(jq -r '.chain.authorized_agents[0]' "$CONFIG")"
MASK=0
while IFS= read -r verdict; do
  case "$verdict" in
    YES) code=1 ;;
    WITHIN_LIMITS) code=2 ;;
    NO) code=3 ;;
    NOT_A_VERIFICATION) code=4 ;;
    NOT_CHECKED) code=5 ;;
    *) echo "anvil-smoke: unknown verdict $verdict" >&2; exit 1 ;;
  esac
  MASK=$(( MASK | (1 << code) ))
done < <(jq -r '.chain.accepted_verdicts[]' "$CONFIG")

echo "  program vkey    $PROGRAM_VKEY"
echo "  commitment id   $COMMITMENT_ID"
echo "  accepted mask   $MASK"
echo "  status zero     $REQUIRE_STATUS_ZERO"
echo "  agent           $AGENT_ID"

echo "== compute the public values and the placeholder bundle =="
BUNDLE="$("$FP_PV" bundle --root "$ROOT" --config "$CONFIG" --proof-hex "$PLACEHOLDER_HEX")"
echo "  bundle ${#BUNDLE} hex characters"

echo "== start anvil on port $PORT =="
anvil --port "$PORT" --silent >/tmp/flashprove-anvil.log 2>&1 &
ANVIL_PID=$!
trap 'kill "$ANVIL_PID" 2>/dev/null || true; wait "$ANVIL_PID" 2>/dev/null || true' EXIT
for _ in $(seq 1 100); do
  if cast chain-id --rpc-url "$RPC" >/dev/null 2>&1; then break; fi
  sleep 0.2
done
cast chain-id --rpc-url "$RPC" >/dev/null || { echo "anvil-smoke: anvil did not start" >&2; exit 1; }

echo "== deploy and call through forge script =="
cd "$ROOT/zkvm/contracts"
DEPLOYER_PRIVATE_KEY="$ANVIL_KEY" \
PROGRAM_VKEY="$PROGRAM_VKEY" \
COMMITMENT_ID="$COMMITMENT_ID" \
ACCEPTED_VERDICTS="$MASK" \
REQUIRE_STATUS_ZERO="$REQUIRE_STATUS_ZERO" \
AGENT_ID="$AGENT_ID" \
TASK_ID="$(cast keccak "flashprove-anvil-smoke")" \
forge script script/AnvilSmoke.s.sol:AnvilSmoke \
  --sig "run(bytes)" "$BUNDLE" \
  --rpc-url "$RPC" --broadcast -vv

echo "anvil-smoke: PASS (the placeholder proof walked the ERC-8274 call path)"
