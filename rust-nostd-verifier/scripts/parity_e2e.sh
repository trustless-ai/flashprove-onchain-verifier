#!/usr/bin/env bash
# S3 end-to-end parity gate: the Rust host against the reference goldens, byte for byte.
#
#   1. the accepted example: the whole stdout against fixtures/golden_stdout.txt, with one
#      normalization (the three stage headings' seconds, which differ from run to run); exit
#      status 0; 105 lines; the YES line and the result-v1 line byte-identical; q_V 136088.
#   2. a tampered proof (byte 2072650 of the proof file, ^= 0x01): the three golden lines and
#      exit status 1.
#   3. a wrong commitment ID (the last two hex digits 83 -> 84): the three golden lines and exit
#      status 1.
#
# Usage: scripts/parity_e2e.sh

set -o pipefail

here=$(cd "$(dirname "$0")/.." && pwd) || exit 1
cd "$here" || exit 1

cargo build --manifest-path "$here/Cargo.toml" --workspace >/dev/null 2>&1 ||
  { echo "parity_e2e: cargo build failed"; exit 1; }
RUST="$here/target/debug/fp-host"
[ -x "$RUST" ] || { echo "parity_e2e: $RUST is missing"; exit 1; }

tmp=$(mktemp -d "${TMPDIR:-/tmp}/fp-parity-e2e.XXXXXX") || exit 1
trap 'rm -rf "$tmp"' EXIT
pass=0
fail=0
ok() { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "FAIL: $*"; }

# `---- stage <name> ---- N thread(s), X.XXX s`: the seconds are run-dependent; the C++ goldens
# and this run are the only normalization that this gate allows.
normalize_timings() {
  sed -E 's/^(---- stage [a-z]+ ---- [0-9]+ thread\(s\), )[0-9.]+ s$/\1<T> s/' "$1"
}

ID=$(tr -d '\n' < fixtures/ID.txt)
CONFIG=fixtures/config
IVK=fixtures/ivk
REQ=fixtures/example.req
Y=fixtures/example.y
PROOF=fixtures/example.proof

# 1. The accepted example.
"$RUST" "$CONFIG" "$IVK" "$REQ" "$Y" "$PROOF" -id "$ID" -q >"$tmp/acc.out" 2>"$tmp/acc.err"
acode=$?
casefail=0
[ "$acode" -eq 0 ] || { casefail=1; echo "  exit $acode, expected 0"; }
[ ! -s "$tmp/acc.err" ] || { casefail=1; echo "  stderr is not empty"; }
lines=$(wc -l <"$tmp/acc.out" | tr -d ' ')
[ "$lines" -eq 105 ] || { casefail=1; echo "  $lines lines, expected 105"; }
grep -qx "YES" "$tmp/acc.out" || { casefail=1; echo "  the last line is not YES"; }
grep -qx "YES" fixtures/golden_stdout.txt || { casefail=1; echo "  the golden has no YES line"; }
grep '^result-v1 ' fixtures/golden_stdout.txt >"$tmp/acc.result.golden"
grep '^result-v1 ' "$tmp/acc.out" >"$tmp/acc.result.actual"
cmp -s "$tmp/acc.result.golden" "$tmp/acc.result.actual" ||
  { casefail=1; echo "  the result-v1 line differs from the golden"; }
grep -Fqx "accounting: hash calls: t, the prover's, is a free variable; q_V, the verifier's own in this run: 136088" "$tmp/acc.out" ||
  { casefail=1; echo "  q_V is not 136088"; }
normalize_timings fixtures/golden_stdout.txt >"$tmp/acc.golden"
normalize_timings "$tmp/acc.out" >"$tmp/acc.actual"
if ! cmp -s "$tmp/acc.golden" "$tmp/acc.actual"; then
  casefail=1
  echo "  stdout differs from fixtures/golden_stdout.txt (stage seconds normalized)"
  diff -u "$tmp/acc.golden" "$tmp/acc.actual" | head -40
fi
if [ "$casefail" -eq 0 ]; then
  ok
  echo "PASS accepted example: 105 lines, exit 0, YES, result-v1 and q_V=136088, full stdout equal"
else
  bad "accepted example"
fi

# 2. A tampered proof, at the one byte that the S3 task book names (offset 2072650, ^= 0x01).
python3 -I - "$PROOF" "$tmp/tampered.proof" <<'PY'
import pathlib
import sys

b = bytearray(pathlib.Path(sys.argv[1]).read_bytes())
if len(b) <= 2072650:
    raise SystemExit("the proof file is shorter than 2072651 bytes")
b[2072650] ^= 0x01
pathlib.Path(sys.argv[2]).write_bytes(b)
PY
"$RUST" "$CONFIG" "$IVK" "$REQ" "$Y" "$tmp/tampered.proof" -id "$ID" -q \
  >"$tmp/tampered.out" 2>"$tmp/tampered.err"
tcode=$?
if [ "$tcode" -eq 1 ] && cmp -s "$tmp/tampered.out" fixtures/golden_negative_tampered.txt; then
  ok
  echo "PASS tampered proof: NO: proof-refused, exit 1, byte-equal to the golden"
else
  bad "tampered proof: expected NO: proof-refused and exit 1"
  echo "  exit $tcode"
  diff -u fixtures/golden_negative_tampered.txt "$tmp/tampered.out" | head -20
fi

# 3. A wrong commitment ID: the last two hex digits 83 -> 84.
case "$ID" in
  *83) WRONG_ID="${ID%??}84" ;;
  *) WRONG_ID="" ;;
esac
if [ -z "$WRONG_ID" ]; then
  bad "wrong ID: fixtures/ID.txt does not end with 83"
else
  "$RUST" "$CONFIG" "$IVK" "$REQ" "$Y" "$PROOF" -id "$WRONG_ID" -q \
    >"$tmp/wrong.out" 2>"$tmp/wrong.err"
  wcode=$?
  if [ "$wcode" -eq 1 ] && cmp -s "$tmp/wrong.out" fixtures/golden_negative_wrong_id.txt; then
    ok
    echo "PASS wrong commitment ID: NO: model-statement, exit 1, byte-equal to the golden"
  else
    bad "wrong ID: expected two id: lines, NO: model-statement and exit 1"
    echo "  exit $wcode"
    diff -u fixtures/golden_negative_wrong_id.txt "$tmp/wrong.out" | head -20
  fi
fi

echo "parity_e2e: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
