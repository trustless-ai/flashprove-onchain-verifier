#!/usr/bin/env bash
# Lane C parity:
#   1. regenerate the exact-arithmetic/codes vectors from the C++ headers and compare the fixture;
#   2. regenerate the plan/accounting dump from the C++ verifier's own `cp_with_configured()` and
#      compare the fixture;
#   3. run the Rust tests: 3,785 arithmetic/code vectors and all four C++ accountings, including the
#      four `result-v1` numbers (128.00 / 96.23 / 38 / 49).
set -o pipefail

here=$(cd "$(dirname "$0")/.." && pwd) || exit 1
root=$(cd "$here/.." && pwd) || exit 1
cd "$root" || exit 1

UPSTREAM=${UPSTREAM:-$root/upstream/FlashProve}
if [ ! -d "$UPSTREAM/blocks" ]; then
  echo "${0##*/}: upstream/FlashProve is not initialised; run: git submodule update --init --depth 1" >&2
  exit 1
fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/fp-numbers.XXXXXX") || exit 1
trap 'rm -rf "$tmp"' EXIT

DEF=(-DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8
     -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"')

echo "parity_numbers: regenerate exact-arithmetic and code vectors"
clang++ -O2 -std=c++17 -I"$UPSTREAM/blocks" -DBLK_FIELD=2 \
  -o "$tmp/numbers_vectors" "$here/scripts/cpp_vectors/numbers_vectors.cpp" ||
  { echo "parity_numbers: FAIL: vector generator build"; exit 1; }
"$tmp/numbers_vectors" >"$tmp/numbers_vectors.txt" ||
  { echo "parity_numbers: FAIL: vector generator run"; exit 1; }
if ! cmp -s "$tmp/numbers_vectors.txt" "$here/fixtures/numbers_vectors.txt"; then
  echo "parity_numbers: FAIL: vectors differ from fixtures/numbers_vectors.txt"
  diff -u "$here/fixtures/numbers_vectors.txt" "$tmp/numbers_vectors.txt" | head -10
  exit 1
fi

echo "parity_numbers: build the C++ verifier as a unit"
clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" "${DEF[@]}" \
  -DCP_VERIFY_AS_A_UNIT -c "$UPSTREAM/verifier/src/cp_verify.cpp" -o "$tmp/cp_verify_unit.o" ||
  { echo "parity_numbers: FAIL: cp_verify unit build"; exit 1; }

echo "parity_numbers: build and run the plan dump"
clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" "${DEF[@]}" \
  -c "$here/scripts/cpp_vectors/dump_plans.cpp" -o "$tmp/dump_plans.o" ||
  { echo "parity_numbers: FAIL: dump tool build"; exit 1; }
clang++ -pthread "$tmp/dump_plans.o" "$tmp/cp_verify_unit.o" -o "$tmp/dump_plans" ||
  { echo "parity_numbers: FAIL: dump tool link"; exit 1; }
"$tmp/dump_plans" "$here/fixtures/config/policy.txt" "$here/fixtures/config/layout.txt" \
  "$here/fixtures/config/KL.bin" >"$tmp/plans_dump.txt" ||
  { echo "parity_numbers: FAIL: plan dump run"; exit 1; }
if ! cmp -s "$tmp/plans_dump.txt" "$here/fixtures/plans_dump.txt"; then
  echo "parity_numbers: FAIL: plan dump differs from fixtures/plans_dump.txt"
  diff -u "$here/fixtures/plans_dump.txt" "$tmp/plans_dump.txt" | head -10
  exit 1
fi

echo "parity_numbers: Rust vector and accounting tests"
cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test numbers_vectors ||
  { echo "parity_numbers: FAIL: numbers_vectors"; exit 1; }
cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test numbers_golden ||
  { echo "parity_numbers: FAIL: numbers_golden"; exit 1; }

echo "parity_numbers: PASS"
