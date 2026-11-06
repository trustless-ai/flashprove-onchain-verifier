#!/usr/bin/env bash
# CLI parity gate for the no_std verifier port.
#
# It checks three things:
#   1. the stored C++ goldens still match a C++ reference built from this checkout;
#   2. the Rust host matches C++ byte for byte (stdout, stderr, exit status) on the CLI cases:
#      command-line errors, unreadable inputs and file/header rejections;
#   3. the Rust host matches the accepted example's 105-line golden.
#
# The C++ side of the accepted example and of the two negative controls is checked here against
# the stored goldens; the Rust side of all three is the end-to-end gate, scripts/parity_e2e.sh.
#
# Usage: scripts/parity.sh            (from anywhere)
#        CPP_BIN=/path/to/cp_verify scripts/parity.sh
#
# The C++ reference is /tmp/tl_cpp_build/cp_verify if present; else /tmp/fp_cpp_build/cp_verify;
# else it is built with the command below (Apple clang works; verifier/build.sh itself needs GNU
# stat/mv and g++ 13 and does not run on macOS).

set -o pipefail

here=$(cd "$(dirname "$0")/.." && pwd) || exit 1
root=$(cd "$here/.." && pwd) || exit 1
cd "$root" || exit 1

UPSTREAM=${UPSTREAM:-$root/upstream/FlashProve}
if [ ! -d "$UPSTREAM/blocks" ]; then
  echo "${0##*/}: upstream/FlashProve is not initialised; run: git submodule update --init --depth 1" >&2
  exit 1
fi

CPP=${CPP_BIN:-/tmp/tl_cpp_build/cp_verify}
if [ ! -x "$CPP" ] && [ -x /tmp/fp_cpp_build/cp_verify ]; then
  CPP=/tmp/fp_cpp_build/cp_verify
fi
if [ ! -x "$CPP" ]; then
  mkdir -p "$(dirname "$CPP")" || exit 1
  echo "parity: C++ reference not found; building $CPP"
  clang++ -O2 -std=c++17 -pthread \
    -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" \
    -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
    -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
    -o "$CPP" "$UPSTREAM/verifier/src/cp_verify.cpp" || { echo "parity: C++ build failed"; exit 1; }
fi
echo "parity: C++ reference: $CPP"

cargo build --manifest-path "$here/Cargo.toml" --workspace >/dev/null 2>&1 ||
  { echo "parity: cargo build failed"; exit 1; }
RUST="$here/target/debug/fp-host"
[ -x "$RUST" ] || { echo "parity: $RUST is missing"; exit 1; }

tmp=$(mktemp -d "${TMPDIR:-/tmp}/fp-parity.XXXXXX") || exit 1
trap 'rm -rf "$tmp"' EXIT
pass=0
fail=0
ok() { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "FAIL: $*"; }

# One CLI case: C++ against its stored golden, then Rust against C++.
run_case() {
  name=$1
  shift
  "$CPP" "$@" >"$tmp/cpp.out" 2>"$tmp/cpp.err"
  ccode=$?
  "$RUST" "$@" >"$tmp/rust.out" 2>"$tmp/rust.err"
  rcode=$?
  casefail=0
  cmp -s "$tmp/cpp.out" "$here/fixtures/cli/$name.out" ||
    { casefail=1; echo "  C++ stdout differs from fixtures/cli/$name.out"; }
  cmp -s "$tmp/cpp.err" "$here/fixtures/cli/$name.err" ||
    { casefail=1; echo "  C++ stderr differs from fixtures/cli/$name.err"; }
  if [ "$ccode" != "$(cat "$here/fixtures/cli/$name.code")" ]; then
    casefail=1
    echo "  C++ exit $ccode differs from the stored golden"
  fi
  if ! cmp -s "$tmp/rust.out" "$tmp/cpp.out"; then
    casefail=1
    echo "  Rust stdout differs"
    diff -u "$tmp/cpp.out" "$tmp/rust.out" | head -20
  fi
  if ! cmp -s "$tmp/rust.err" "$tmp/cpp.err"; then
    casefail=1
    echo "  Rust stderr differs"
    diff -u "$tmp/cpp.err" "$tmp/rust.err" | head -20
  fi
  if [ "$rcode" != "$ccode" ]; then
    casefail=1
    echo "  Rust exit $rcode differs from C++ $ccode"
  fi
  if [ "$casefail" -eq 0 ]; then
    ok
    printf 'PASS %s\n' "$name"
  else
    bad "case $name"
  fi
}

# `---- stage <name> ---- N thread(s), X.XXX s`: the seconds are run-dependent.
normalize_timings() {
  sed -E 's/^(---- stage [a-z]+ ---- [0-9]+ thread\(s\), )[0-9.]+ s$/\1<T> s/' "$1"
}

ID=79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183
CONFIG=rust-nostd-verifier/fixtures/config
IVK=rust-nostd-verifier/fixtures/ivk
REQ=rust-nostd-verifier/fixtures/example.req
Y=rust-nostd-verifier/fixtures/example.y
PROOF=rust-nostd-verifier/fixtures/example.proof

# 1. CLI cases from the manifest.
while IFS=$'\t' read -r -a parts; do
  [ "${#parts[@]}" -eq 0 ] && continue
  name=${parts[0]}
  args=()
  i=1
  while [ "$i" -lt "${#parts[@]}" ]; do
    args[${#args[@]}]=${parts[$i]}
    i=$((i + 1))
  done
  run_case "$name" "${args[@]}"
done <"$here/fixtures/cases.tsv"

# 2. C++ accepted example against the stored 105-line golden (timings normalized).
"$CPP" "$CONFIG" "$IVK" "$REQ" "$Y" "$PROOF" -id "$ID" -q >"$tmp/acc.out" 2>"$tmp/acc.err"
acode=$?
normalize_timings "$here/fixtures/golden_stdout.txt" >"$tmp/acc.golden"
normalize_timings "$tmp/acc.out" >"$tmp/acc.actual"
if [ "$acode" -eq 0 ] &&
  [ ! -s "$tmp/acc.err" ] &&
  [ "$(tail -n 1 "$tmp/acc.out")" = "YES" ] &&
  cmp -s "$tmp/acc.golden" "$tmp/acc.actual"; then
  ok
  echo "PASS accepted example (C++ against golden_stdout.txt)"
else
  bad "accepted example: C++ against golden_stdout.txt"
  diff -u "$tmp/acc.golden" "$tmp/acc.actual" | head -20
fi

# 3. Tampered proof (offset 2072650, byte ^= 0x01): last three lines.
python3 -I - "$here/fixtures/example.proof" "$tmp/tampered.proof" <<'PY'
import pathlib
import sys

b = bytearray(pathlib.Path(sys.argv[1]).read_bytes())
b[2072650] ^= 0x01
pathlib.Path(sys.argv[2]).write_bytes(b)
PY
"$CPP" "$CONFIG" "$IVK" "$REQ" "$Y" "$tmp/tampered.proof" -id "$ID" -q \
  >"$tmp/tampered.out" 2>"$tmp/tampered.err"
tcode=$?
tail -n 3 "$tmp/tampered.out" >"$tmp/tampered.tail"
if [ "$tcode" -eq 1 ] && cmp -s "$tmp/tampered.tail" "$here/fixtures/golden_negative_tampered.txt"; then
  ok
  echo "PASS tampered proof (C++ against golden_negative_tampered.txt)"
else
  bad "tampered proof: expected NO: proof-refused and exit 1"
  diff -u "$here/fixtures/golden_negative_tampered.txt" "$tmp/tampered.tail" | head -20
fi

# 4. Wrong commitment ID (last hex digit 3 -> 4): the three id/NO lines.
WRONG_ID="${ID%?}4"
"$CPP" "$CONFIG" "$IVK" "$REQ" "$Y" "$PROOF" -id "$WRONG_ID" -q \
  >"$tmp/wrong.out" 2>"$tmp/wrong.err"
wcode=$?
if [ "$wcode" -eq 1 ] && cmp -s "$tmp/wrong.out" "$here/fixtures/golden_negative_wrong_id.txt"; then
  ok
  echo "PASS wrong commitment ID (C++ against golden_negative_wrong_id.txt)"
else
  bad "wrong ID: expected NO: model-statement and exit 1"
  diff -u "$here/fixtures/golden_negative_wrong_id.txt" "$tmp/wrong.out" | head -20
fi

# 5. The Rust host on the accepted example: the same 105 lines as the golden (timings
#    normalized) and a YES. The negative controls are scripts/parity_e2e.sh's.
"$RUST" "$CONFIG" "$IVK" "$REQ" "$Y" "$PROOF" -id "$ID" -q >"$tmp/rust_acc.out" 2>"$tmp/rust_acc.err"
rcode=$?
normalize_timings "$tmp/rust_acc.out" >"$tmp/rust_acc.norm"
if [ "$rcode" -eq 0 ] &&
  [ ! -s "$tmp/rust_acc.err" ] &&
  [ "$(tail -n 1 "$tmp/rust_acc.out")" = "YES" ] &&
  cmp -s "$tmp/acc.golden" "$tmp/rust_acc.norm"; then
  ok
  echo "PASS Rust host on the accepted example (against golden_stdout.txt)"
else
  bad "Rust host differs on the accepted example"
  diff -u "$tmp/acc.golden" "$tmp/rust_acc.norm" | head -20
fi

echo "parity: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
