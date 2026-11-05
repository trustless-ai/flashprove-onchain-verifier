#!/usr/bin/env bash
# Lane A parity: regenerate the C++ field vectors and run the Rust comparison.
set -o pipefail

here=$(cd "$(dirname "$0")/.." && pwd) || exit 1
root=$(cd "$here/.." && pwd) || exit 1
cd "$root" || exit 1

tmp=$(mktemp -d "${TMPDIR:-/tmp}/fp-field.XXXXXX") || exit 1
trap 'rm -rf "$tmp"' EXIT

echo "parity_field: building the C++ vector generator"
clang++ -O2 -std=c++17 -Iblocks -DBLK_FIELD=2 \
  -o "$tmp/field_vectors" "$here/scripts/cpp_vectors/field_vectors.cpp" ||
  { echo "parity_field: C++ build failed"; exit 1; }

"$tmp/field_vectors" >"$tmp/field_vectors.txt" ||
  { echo "parity_field: C++ generator failed"; exit 1; }

if ! cmp -s "$tmp/field_vectors.txt" "$here/fixtures/field_vectors.txt"; then
  echo "parity_field: FAIL: regenerated vectors differ from fixtures/field_vectors.txt"
  diff -u "$here/fixtures/field_vectors.txt" "$tmp/field_vectors.txt" | head -20
  exit 1
fi
echo "parity_field: generated vectors match fixtures/field_vectors.txt"

cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test field_vectors ||
  { echo "parity_field: FAIL: Rust vector test"; exit 1; }

echo "parity_field: PASS"
