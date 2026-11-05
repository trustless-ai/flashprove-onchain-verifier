#!/usr/bin/env bash
# S2b parity: the base blocks
#   S2b-1: iop/message.h, chain/{chain,public,rounds}.h, tree/* (verifier side), code/*;
#   S2b-2: algebraic and fold blocks (tensor, hp, psc, mask, bat, fold, cs, iopp, send, ...);
#   S2b-3: commitment and lookup blocks (foldeq, lin, link, member, lkp, rng, wf).
#
#   1. each C++ vector tool is built from the checkout's headers and run;
#   2. its output is compared byte for byte with the stored fixture;
#   3. the Rust tests replay the vectors;
#   4. the whole workspace builds and its tests pass;
#   5. fp-core is scanned for `use std`, `extern crate std` and `static mut`.
set -o pipefail

here=$(cd "$(dirname "$0")/.." && pwd) || exit 1
root=$(cd "$here/.." && pwd) || exit 1
cd "$root" || exit 1

tmp=$(mktemp -d "${TMPDIR:-/tmp}/fp-base.XXXXXX") || exit 1
trap 'rm -rf "$tmp"' EXIT

pass=0
fail=0
ok() {
  pass=$((pass + 1))
  echo "PASS $1"
}
bad() {
  fail=$((fail + 1))
  echo "FAIL $1"
}

# tool  fixture  flags...
check_cpp() {
  local tool=$1 fixture=$2
  shift 2
  echo "parity_base: building $tool"
  clang++ -O2 -std=c++17 -Iblocks -DBLK_FIELD=2 "$@" \
    -o "$tmp/$tool" "$here/scripts/cpp_vectors/$tool.cpp" ||
    { bad "$tool: C++ build"; return; }
  "$tmp/$tool" >"$tmp/$tool.txt" ||
    { bad "$tool: C++ run"; return; }
  if cmp -s "$tmp/$tool.txt" "$here/fixtures/$fixture"; then
    ok "$tool: vectors match fixtures/$fixture"
  else
    bad "$tool: vectors differ from fixtures/$fixture"
    diff -u "$here/fixtures/$fixture" "$tmp/$tool.txt" | head -20
  fi
}

check_cpp message_vectors message_vectors.txt
check_cpp chain_vectors chain_vectors.txt -DBLK_COUNT_HASH_CALLS=1
check_cpp tree_code_vectors tree_code_vectors.txt
check_cpp rounds_vectors rounds_vectors.txt
check_cpp tensor_vectors tensor_vectors.txt
check_cpp hp_fold_vectors hp_fold_vectors.txt
check_cpp fold_output_vectors fold_output_vectors.txt
check_cpp iop_core_vectors iop_core_vectors.txt
check_cpp iop_data_vectors iop_data_vectors.txt
check_cpp components_vectors components_vectors.txt
check_cpp send_vectors send_vectors.txt
check_cpp foldeq_vectors foldeq_vectors.txt
check_cpp lin_vectors lin_vectors.txt
check_cpp link_member_vectors link_member_vectors.txt
check_cpp lkp_vectors lkp_vectors.txt
check_cpp rng_vectors rng_vectors.txt
check_cpp wf_vectors wf_vectors.txt

for test in message_vectors chain_vectors tree_code_vectors rounds_vectors tensor_vectors hp_fold_vectors fold_output_vectors iop_core_vectors iop_data_vectors components_vectors send_vectors foldeq_vectors lin_vectors link_member_vectors lkp_vectors rng_vectors wf_vectors; do
  if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test "$test" >"$tmp/$test.log" 2>&1; then
    ok "Rust $test"
  else
    bad "Rust $test"
    tail -20 "$tmp/$test.log"
  fi
done

echo "parity_base: cargo build --workspace"
if cargo build --manifest-path "$here/Cargo.toml" --workspace >"$tmp/build.log" 2>&1; then
  ok "cargo build --workspace"
else
  bad "cargo build --workspace"
  tail -20 "$tmp/build.log"
fi

echo "parity_base: cargo test --workspace"
if cargo test --manifest-path "$here/Cargo.toml" --workspace >"$tmp/test.log" 2>&1; then
  ok "cargo test --workspace"
else
  bad "cargo test --workspace"
  tail -30 "$tmp/test.log"
fi

echo "parity_base: fp-core no_std scan"
if grep -rnE '(^|[^A-Za-z_])use std(::|;)|extern crate std|static mut' "$here/fp-core/src" >"$tmp/scan.log"; then
  bad "fp-core holds std or a mutable static"
  cat "$tmp/scan.log"
else
  ok "fp-core: no use std, extern crate std or static mut"
fi

echo "parity_base: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
