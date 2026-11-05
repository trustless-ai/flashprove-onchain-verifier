#!/usr/bin/env bash
# Deploy the ERC-8274 stack with the parameters in the JSON configuration.
#
# Required in the environment: DEPLOYER_PRIVATE_KEY.
# Everything else comes from the configuration's `chain` section and the vkey record; the one
# exception is `chain.sp1_verifier`, which must be the deployed SP1 verifier for this chain.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CONFIG="${CONFIG:-$ROOT/zkvm/config/flashprove.json}"

for tool in jq forge cast; do
  command -v "$tool" >/dev/null 2>&1 || { echo "deploy: missing $tool" >&2; exit 1; }
done
: "${DEPLOYER_PRIVATE_KEY:?set DEPLOYER_PRIVATE_KEY}"

PROGRAM_VKEY="$(jq -r '.chain.program_vkey // empty' "$CONFIG")"
if [ -z "$PROGRAM_VKEY" ]; then
  RECORD="$(jq -r '.program.vkey_record' "$CONFIG")"
  PROGRAM_VKEY="$(jq -r '.sp1.vkey_bytes32' "$ROOT/$RECORD")"
fi
SP1_VERIFIER="${SP1_VERIFIER:-$(jq -r '.chain.sp1_verifier // empty' "$CONFIG")}"
[ -n "$SP1_VERIFIER" ] || { echo "deploy: set chain.sp1_verifier in $CONFIG or pass SP1_VERIFIER" >&2; exit 1; }
COMMITMENT_ID="$(jq -r '.chain.commitment_id' "$CONFIG")"
RPC_URL="${RPC_URL:-$(jq -r '.chain.rpc_url' "$CONFIG")}"
REQUIRE_STATUS_ZERO="$(jq -r '.chain.require_status_zero' "$CONFIG")"
AUTHORIZED_AGENTS="$(jq -r '.chain.authorized_agents | join(",")' "$CONFIG")"
MASK=0
while IFS= read -r verdict; do
  case "$verdict" in
    YES) code=1 ;;
    WITHIN_LIMITS) code=2 ;;
    NO) code=3 ;;
    NOT_A_VERIFICATION) code=4 ;;
    NOT_CHECKED) code=5 ;;
    *) echo "deploy: unknown verdict $verdict" >&2; exit 1 ;;
  esac
  MASK=$(( MASK | (1 << code) ))
done < <(jq -r '.chain.accepted_verdicts[]' "$CONFIG")

echo "deploy: rpc $RPC_URL"
echo "  sp1 verifier   $SP1_VERIFIER"
echo "  program vkey   $PROGRAM_VKEY"
echo "  commitment id  $COMMITMENT_ID"
echo "  accepted mask  $MASK"
echo "  status zero    $REQUIRE_STATUS_ZERO"
echo "  agents         $AUTHORIZED_AGENTS"

cd "$ROOT/zkvm/contracts"
DEPLOYER_PRIVATE_KEY="$DEPLOYER_PRIVATE_KEY" \
SP1_VERIFIER="$SP1_VERIFIER" \
PROGRAM_VKEY="$PROGRAM_VKEY" \
COMMITMENT_ID="$COMMITMENT_ID" \
ACCEPTED_VERDICTS="$MASK" \
REQUIRE_STATUS_ZERO="$REQUIRE_STATUS_ZERO" \
AUTHORIZED_AGENTS="$AUTHORIZED_AGENTS" \
forge script script/Deploy.s.sol:Deploy --rpc-url "$RPC_URL" --broadcast -vv
