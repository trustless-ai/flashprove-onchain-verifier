#!/usr/bin/env bash
# Lane B parity:
#   1. the repository's Python reference scripts regenerate their own vectors;
#   2. the Python F reference regenerates fixtures/earlier_hash_f_vectors.txt;
#   3. the C++ counter tool regenerates fixtures/hash_counts.txt;
#   4. the Rust tests recompute every vector and both counters.
set -o pipefail

here=$(cd "$(dirname "$0")/.." && pwd) || exit 1
root=$(cd "$here/.." && pwd) || exit 1
cd "$root" || exit 1

tmp=$(mktemp -d "${TMPDIR:-/tmp}/fp-hash.XXXXXX") || exit 1
trap 'rm -rf "$tmp"' EXIT

echo "parity_hash: Python BLAKE2b self-test (RFC 7693 + hashlib)"
python3 verifier/tests/known_answers/blake2b_f.py >"$tmp/blake_selftest.txt" 2>&1 ||
  { echo "parity_hash: FAIL: blake2b_f.py self-test"; tail -20 "$tmp/blake_selftest.txt"; exit 1; }

echo "parity_hash: regenerate the Python F vectors"
python3 verifier/tests/known_answers/blake2b_f.py 200 20261105 >"$tmp/f_vectors.txt" ||
  { echo "parity_hash: FAIL: blake2b_f.py vectors"; exit 1; }
if ! cmp -s "$tmp/f_vectors.txt" "$here/fixtures/earlier_hash_f_vectors.txt"; then
  echo "parity_hash: FAIL: F vectors differ from fixtures/earlier_hash_f_vectors.txt"
  diff -u "$here/fixtures/earlier_hash_f_vectors.txt" "$tmp/f_vectors.txt" | head -10
  exit 1
fi

echo "parity_hash: check verifier/tests/hash_vectors.txt with format_hash.py"
python3 verifier/tests/known_answers/format_hash.py --hold verifier/tests/hash_vectors.txt \
  >"$tmp/format_hash.txt" 2>&1 ||
  { echo "parity_hash: FAIL: format_hash.py --hold"; tail -20 "$tmp/format_hash.txt"; exit 1; }

echo "parity_hash: regenerate blocks/hash/tests/mode_vectors.txt"
python3 blocks/hash/tests/mode_vectors.py >"$tmp/mode_vectors.txt" 2>&1 ||
  { echo "parity_hash: FAIL: mode_vectors.py"; exit 1; }
if ! cmp -s "$tmp/mode_vectors.txt" blocks/hash/tests/mode_vectors.txt; then
  echo "parity_hash: FAIL: regenerated mode vectors differ"
  diff -u blocks/hash/tests/mode_vectors.txt "$tmp/mode_vectors.txt" | head -10
  exit 1
fi

echo "parity_hash: regenerate the C++ hash counts"
clang++ -O2 -std=c++17 -Iverifier/src -Iblocks -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 \
  -o "$tmp/hash_counters" "$here/scripts/cpp_vectors/hash_counters.cpp" ||
  { echo "parity_hash: FAIL: C++ counter build"; exit 1; }
"$tmp/hash_counters" >"$tmp/hash_counts.txt" ||
  { echo "parity_hash: FAIL: C++ counter run"; exit 1; }
if ! cmp -s "$tmp/hash_counts.txt" "$here/fixtures/hash_counts.txt"; then
  echo "parity_hash: FAIL: counters differ from fixtures/hash_counts.txt"
  diff -u "$here/fixtures/hash_counts.txt" "$tmp/hash_counts.txt" | head -10
  exit 1
fi

echo "parity_hash: Rust vector and counter tests"
cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test hash_vectors ||
  { echo "parity_hash: FAIL: hash_vectors"; exit 1; }
cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test hash_counters ||
  { echo "parity_hash: FAIL: hash_counters"; exit 1; }

echo "parity_hash: PASS"
