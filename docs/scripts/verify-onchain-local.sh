#!/usr/bin/env bash
# Verify an accepted FlashProve bundle on a disposable local Anvil chain.
#
# IMPORTANT: OUT must be a fresh dedicated directory. This script writes
# $OUT/onchain and will refuse to overwrite an existing evidence set unless
# ALLOW_OVERWRITE=1 is explicitly set.
#
# Required:
#   ROOT                  repository root (contains contracts/ and config/)
#   OUT                   output root (the accepted run directory)
#   SP1_CONTRACTS         root of the sp1-contracts v6.1.0 checkout
#   DEPLOYER_PRIVATE_KEY  disposable local key (never commit it)
#
# Optional:
#   BUNDLE                default: $OUT/accepted/bundle.bin
#   SUMMARY               default: $OUT/accepted/summary.json
#   CONFIG                default: $ROOT/config/flashprove.json
#   RPC / PORT            default: http://127.0.0.1:8545 / 8545
#   PROOF_TAMPER_OFFSET   default: 355
#   PV_TAMPER_OFFSET      default: 6710
#
# This script deploys the official v6.1.0 verifier and the two wrapper contracts,
# sends the valid bundle plus three negative controls, checks usedTasks separately
# for every task, and recomputes the event verificationDigest. It does not create
# a proof.
set -euo pipefail

: "${ROOT:?set ROOT}"
: "${OUT:?set OUT}"
: "${SP1_CONTRACTS:?set SP1_CONTRACTS}"
: "${DEPLOYER_PRIVATE_KEY:?set DEPLOYER_PRIVATE_KEY (disposable local key)}"

BUNDLE=${BUNDLE:-$OUT/accepted/bundle.bin}
SUMMARY=${SUMMARY:-$OUT/accepted/summary.json}
CONFIG=${CONFIG:-$ROOT/config/flashprove.json}
PORT=${PORT:-8545}
RPC=${RPC:-http://127.0.0.1:$PORT}
KEEP_ANVIL=${KEEP_ANVIL:-0}
OUTDIR="$OUT/onchain"
SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

fail() { echo "verify-onchain-local: FAIL: $*" >&2; exit 1; }
if [ -e "$OUTDIR/stack.json" ] || [ -e "$OUTDIR/valid.summary.json" ] || [ -e "$OUTDIR/tamper-proof.fields.json" ]; then
  [ "${ALLOW_OVERWRITE:-0}" = "1" ] || fail "OUT/onchain already contains evidence; choose a fresh OUT or set ALLOW_OVERWRITE=1"
fi
mkdir -p "$OUTDIR"
need() { command -v "$1" >/dev/null 2>&1 || fail "missing $1"; }
[ -f "$SCRIPT_DIR/bundle-tools.py" ] || fail "missing $SCRIPT_DIR/bundle-tools.py"
need jq; need cast; need forge; need anvil; need xxd; need python3

[ -s "$BUNDLE" ] || fail "missing bundle $BUNDLE"
[ -s "$SUMMARY" ] || fail "missing summary $SUMMARY"
INPUT_HASH=$(jq -r '.input_digest // empty' "$SUMMARY")
OUTPUT_HASH=$(jq -r '.output_hash // empty' "$SUMMARY")
BUNDLE_BYTES=$(jq -r '.bundle_bytes // empty' "$SUMMARY")
[ -n "$INPUT_HASH" ] && [ -n "$OUTPUT_HASH" ] && [ -n "$BUNDLE_BYTES" ] || fail "summary lacks input/output/bundle fields"
[ "$(stat -c%s "$BUNDLE")" = "$BUNDLE_BYTES" ] || fail "bundle size does not match summary"

VKEY=${VKEY:-$(jq -r '.sp1.vkey_bytes32' "$ROOT/$(jq -r '.program.vkey_record' "$CONFIG")")}
COMMITMENT=${COMMITMENT:-$(jq -r '.chain.commitment_id' "$CONFIG")}
AGENT_ID=${AGENT_ID:-$(jq -r '.chain.authorized_agents[0]' "$CONFIG")}
[ -n "$VKEY" ] && [ -n "$COMMITMENT" ] && [ -n "$AGENT_ID" ] || fail "configuration lacks vkey/commitment/agent"

MASK=0
while IFS= read -r verdict; do
  case "$verdict" in
    YES) code=1 ;; WITHIN_LIMITS) code=2 ;; NO) code=3 ;;
    NOT_A_VERIFICATION) code=4 ;; NOT_CHECKED) code=5 ;;
    *) fail "unknown accepted verdict $verdict" ;;
  esac
  MASK=$(( MASK | (1 << code) ))
done < <(jq -r '.chain.accepted_verdicts[]' "$CONFIG")
REQUIRE_ZERO=$(jq -r '.chain.require_status_zero' "$CONFIG")

echo "== build the official verifier =="
( cd "$SP1_CONTRACTS/contracts" && forge build src/v6.1.0/SP1VerifierGroth16.sol ) >"$OUTDIR/official-build.log" 2>&1 \
  || { cat "$OUTDIR/official-build.log" >&2; fail "official verifier build"; }
OFF_ART="$SP1_CONTRACTS/contracts/out/SP1VerifierGroth16.sol/SP1Verifier.json"
[ -s "$OFF_ART" ] || fail "official artifact not found at $OFF_ART"
OFF_BYTECODE=$(jq -r '.bytecode.object' "$OFF_ART")
[ "$OFF_BYTECODE" != "0x" ] || fail "official artifact has no creation bytecode"

echo "== build the wrapper contracts =="
( cd "$ROOT/contracts" && forge build ) >"$OUTDIR/wrapper-build.log" 2>&1 \
  || { cat "$OUTDIR/wrapper-build.log" >&2; fail "wrapper build"; }
ZK_ART="$ROOT/contracts/out/FlashProveZKVerifier.sol/FlashProveZKVerifier.json"
AG_ART="$ROOT/contracts/out/ExampleAgentVerifier.sol/ExampleAgentVerifier.json"
[ -s "$ZK_ART" ] && [ -s "$AG_ART" ] || fail "wrapper artifacts missing"

echo "== start disposable anvil on port $PORT =="
anvil --port "$PORT" --silent >"$OUTDIR/anvil.log" 2>&1 &
ANVIL_PID=$!
cleanup() {
  if [ "$KEEP_ANVIL" = "1" ]; then
    echo "anvil left running: pid=$ANVIL_PID rpc=$RPC"
  else
    kill "$ANVIL_PID" 2>/dev/null || true
    wait "$ANVIL_PID" 2>/dev/null || true
  fi
}
trap cleanup EXIT
for _ in $(seq 1 100); do cast chain-id --rpc-url "$RPC" >/dev/null 2>&1 && break; sleep 0.2; done
[ "$(cast chain-id --rpc-url "$RPC")" = "31337" ] || fail "anvil chain id is not 31337"

deploy() { # label artifact constructor-args
  local label=$1 artifact=$2 args=${3:-}
  local code; code=$(jq -r '.bytecode.object' "$artifact")
  [ "$code" != "0x" ] || fail "$label has no creation bytecode"
  local receipt; receipt=$(cast send --rpc-url "$RPC" --private-key "$DEPLOYER_PRIVATE_KEY" --json --create "${code}${args}")
  printf '%s\n' "$receipt" >"$OUTDIR/$label-deploy.json"
  jq -r '.contractAddress' "$OUTDIR/$label-deploy.json"
}

echo "== deploy official SP1 verifier =="
SP1_VERIFIER=$(deploy official "$OFF_ART")
[ -n "$SP1_VERIFIER" ] && [ "$SP1_VERIFIER" != "null" ] || fail "official deployment address missing"
[ "$(cast call "$SP1_VERIFIER" 'VERSION()(string)' --rpc-url "$RPC")" = '"v6.1.0"' ] || fail "official VERSION mismatch"
[ "$(cast call "$SP1_VERIFIER" 'VERIFIER_HASH()(bytes32)' --rpc-url "$RPC")" = "0x4388a21c687fdd5f218d7e3d13190cac4c5355818d3605fd5fb811df468ee696" ] || fail "official VERIFIER_HASH mismatch"
[ "$(cast call "$SP1_VERIFIER" 'VK_ROOT()(bytes32)' --rpc-url "$RPC")" = "0x002f850ee998974d6cc00e50cd0814b098c05bfade466d28573240d057f25352" ] || fail "official VK_ROOT mismatch"

echo "== deploy FlashProveZKVerifier =="
ZK_ARGS=$(cast abi-encode 'f(address)' "$SP1_VERIFIER" | cut -c3-)
ZK_VERIFIER=$(deploy zk "$ZK_ART" "$ZK_ARGS")
[ -n "$ZK_VERIFIER" ] && [ "$ZK_VERIFIER" != "null" ] || fail "ZK deployment address missing"

echo "== deploy ExampleAgentVerifier =="
METADATA=$(cast abi-encode 'f(bytes32)' "$VKEY")
AG_ARGS=$(cast abi-encode 'f(address,bytes,bytes32,uint16,bool,bytes32[])' \
  "$ZK_VERIFIER" "$METADATA" "$COMMITMENT" "$MASK" "$REQUIRE_ZERO" "[$AGENT_ID]" | cut -c3-)
AGENT=$(deploy agent "$AG_ART" "$AG_ARGS")
[ -n "$AGENT" ] && [ "$AGENT" != "null" ] || fail "agent deployment address missing"
[ "$(cast call "$AGENT" 'usedTasks(bytes32)(bool)' "$(cast keccak 'never-used')" --rpc-url "$RPC")" = "false" ] || fail "fresh usedTasks is not false"

write_stack() {
  jq -n --arg official "$SP1_VERIFIER" --arg zk "$ZK_VERIFIER" --arg agent "$AGENT" \
    --arg rpc "$RPC" --arg vkey "$VKEY" --arg commitment "$COMMITMENT" --arg agent_id "$AGENT_ID" \
    --arg mask "$MASK" --arg anvil_pid "$ANVIL_PID" \
    '{official:$official,zk:$zk,agent:$agent,rpc:$rpc,vkey:$vkey,commitment:$commitment,agent_id:$agent_id,mask:($mask|tonumber),anvil_pid:($anvil_pid|tonumber)}' \
    >"$OUTDIR/stack.json"
}
# Always replace stack.json with this run's current addresses/PID. A full run must
# not leave a stale Stage-4 PID for a later manual Stage-6 stop.
write_stack
if [ "${STACK_ONLY:-0}" = "1" ]; then
  echo "STACK_ONLY: wrote $OUTDIR/stack.json"
  exit 0
fi

TOPIC0=$(cast keccak 'VerificationCompleted(bytes32,bytes32,bytes32,bool,bytes32,bytes32,bytes32,uint256,bytes,bytes)')

run_case() { # label task bundle expect_valid expect_used
  local label=$1 task=$2 bundle=$3 expect_valid=$4 expect_used=$5
  local bhex send txhash txjson rec log data valid digest topic_digest used ts profile instance chain pre
  bhex="0x$(xxd -p -c 999999 "$bundle")"
  send=$(cast send "$AGENT" 'verify(bytes32,bytes32,bytes32,bytes32,bytes)' \
    "$task" "$AGENT_ID" "$INPUT_HASH" "$OUTPUT_HASH" "$bhex" \
    --rpc-url "$RPC" --private-key "$DEPLOYER_PRIVATE_KEY" --json)
  printf '%s\n' "$send" >"$OUTDIR/$label.send.json"
  txhash=$(jq -r '.transactionHash' <<<"$send")
  txjson=$(cast tx "$txhash" --rpc-url "$RPC" --json)
  printf '%s\n' "$txjson" >"$OUTDIR/$label.tx.json"
  rec=$(cast receipt "$txhash" --rpc-url "$RPC" --json)
  printf '%s\n' "$rec" >"$OUTDIR/$label.receipt.json"
  # Actual transaction input must ABI-decode to the tested bundle byte-for-byte.
  python3 "$SCRIPT_DIR/bundle-tools.py" check-tx \
    "$OUTDIR/$label.tx.json" "$bundle" "$OUTDIR/$label.input-check.json" >/dev/null
  log=$(jq -c --arg t "$TOPIC0" '.logs[] | select(.topics[0] == $t)' <<<"$rec" | head -1)
  [ -n "$log" ] || fail "$label emitted no VerificationCompleted event"
  data=$(jq -r '.data' <<<"$log")
  topic_digest=$(jq -r '.topics[3]' <<<"$log")
  local dec; dec=$(cast abi-decode 'f(bool,bytes32,bytes32,bytes32,uint256,bytes,bytes)(bool,bytes32,bytes32,bytes32,uint256,bytes,bytes)' "$data")
  valid=$(sed -n '1p' <<<"$dec")
  ts=$(sed -n '5p' <<<"$dec" | awk '{print $1}')
  profile=$(sed -n '4p' <<<"$dec")
  instance=$(sed -n '6p' <<<"$dec")
  chain=$(sed -n '7p' <<<"$dec")
  [ "$(sed -n '2p' <<<"$dec")" = "$INPUT_HASH" ] || fail "$label inputHash mismatch"
  [ "$(sed -n '3p' <<<"$dec")" = "$OUTPUT_HASH" ] || fail "$label outputHash mismatch"
  pre=$(cast abi-encode 'f(bytes32,bytes32,bytes32,bytes32,bool,bytes32,uint256,bytes,bytes)' \
    "$task" "$AGENT_ID" "$INPUT_HASH" "$OUTPUT_HASH" "$valid" "$profile" "$ts" "$instance" "$chain")
  digest=$(cast keccak "$pre")
  [ "$digest" = "$topic_digest" ] || fail "$label verificationDigest mismatch: $digest != $topic_digest"
  used=$(cast call "$AGENT" 'usedTasks(bytes32)(bool)' "$task" --rpc-url "$RPC")
  [ "$valid" = "$expect_valid" ] || fail "$label valid=$valid expected $expect_valid"
  [ "$used" = "$expect_used" ] || fail "$label usedTasks=$used expected $expect_used"
  jq -n --arg label "$label" --arg task "$task" --arg tx "$txhash" --arg valid "$valid" --arg used "$used" \
    --arg digest "$digest" --arg topic "$topic_digest" \
    '{label:$label,task:$task,tx:$tx,valid:($valid=="true"),usedTasks:($used=="true"),digest:$digest,digest_topic:$topic,input_check:($label+".input-check.json")}' \
    >"$OUTDIR/$label.summary.json"
  echo "$label valid=$valid usedTasks=$used digest=$digest"
}

echo "== positive and negative matrix =="
# ABI-decode the bundle into its two fields, flip exactly one byte inside the
# proof or public-values field, and re-encode. The helper asserts the target field
# changed once and the other field is byte-identical.
python3 "$SCRIPT_DIR/bundle-tools.py" tamper "$BUNDLE" "$OUTDIR/tamper-proof.bin" proof "$OUTDIR/tamper-proof.fields.json"
python3 "$SCRIPT_DIR/bundle-tools.py" tamper "$BUNDLE" "$OUTDIR/tamper-pv.bin" pv "$OUTDIR/tamper-pv.fields.json"

TASK_PROOF=$(cast keccak "flashprove-local-tamper-proof-$(date +%s)")
TASK_PV=$(cast keccak "flashprove-local-tamper-pv-$(date +%s)")
TASK_OK=$(cast keccak "flashprove-local-valid-$(date +%s)")

run_case tamper-proof "$TASK_PROOF" "$OUTDIR/tamper-proof.bin" false false
run_case tamper-pv "$TASK_PV" "$OUTDIR/tamper-pv.bin" false false
run_case valid "$TASK_OK" "$BUNDLE" true true
run_case repeat "$TASK_OK" "$BUNDLE" false true

echo "PASS: local verifier closure and all negative controls"
