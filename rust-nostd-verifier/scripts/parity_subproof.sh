#!/usr/bin/env bash
# Sub-proof parity: the shared verifier core, the transcript adapter, and the four public tables
#
#   1. the C++ common-vector tool is built from the checkout's verifier translation unit and its
#      output is compared with fixtures/common_vectors.txt; the Rust test replays it;
#   2. the transcript adapter is exercised on a real VerifierRounds;
#   3. the C++ table-vector tool is built from the checkout's verifier translation unit, run on the
#      fixture parameter file, and its output is compared with fixtures/table_vectors.txt;
#   4. the Rust test rebuilds all four tables, recomputes the digests and replays the gate,
#      including the four mutated digests' rejection names;
#   5. the C++ sub-proof vector tool is built and its output compared with
#      fixtures/subproof_vectors.txt: the engine, packing, smallness planning, lookup forest, PSC
#      row and the sumcheck slot counts;
#   6. the Rust replay of that tool, and the transcript-driven sub-proof tests on a real chain;
#   7. the request frame: the C++ tool proves the toy requests of blocks/iop/tests/req_rows_cases.h,
#      and its verdicts (honest, spoiled, false target, a missing close or moment) and fault names
#      are replayed by the Rust frame (ReqFrame, req_row, ChainCheck);
#   8. the whole workspace builds and its tests pass;
#   9. fp-core is scanned for `use std`, `extern crate std` and `static mut`.
set -o pipefail

here=$(cd "$(dirname "$0")/.." && pwd) || exit 1
root=$(cd "$here/.." && pwd) || exit 1
cd "$root" || exit 1

UPSTREAM=${UPSTREAM:-$root/upstream/FlashProve}
if [ ! -d "$UPSTREAM/blocks" ]; then
  echo "${0##*/}: upstream/FlashProve is not initialised; run: git submodule update --init --depth 1" >&2
  exit 1
fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/fp-tables.XXXXXX") || exit 1
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

echo "parity_subproof: building common_vectors"
if clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" -DBLK_FIELD=2 \
  -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o "$tmp/common_vectors" "$here/scripts/cpp_vectors/common_vectors.cpp"; then
  if "$tmp/common_vectors" >"$tmp/common_vectors.txt"; then
    if cmp -s "$tmp/common_vectors.txt" "$here/fixtures/common_vectors.txt"; then
      ok "common_vectors: output matches fixtures/common_vectors.txt"
    else
      bad "common_vectors: output differs from fixtures/common_vectors.txt"
      diff -u "$here/fixtures/common_vectors.txt" "$tmp/common_vectors.txt" | head -20
    fi
  else
    bad "common_vectors: C++ run"
  fi
else
  bad "common_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test common_vectors \
  >"$tmp/common_vectors.log" 2>&1; then
  ok "Rust common_vectors"
else
  bad "Rust common_vectors"
  tail -30 "$tmp/common_vectors.log"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test transcript_tests \
  >"$tmp/transcript_tests.log" 2>&1; then
  ok "Rust transcript_tests"
else
  bad "Rust transcript_tests"
  tail -30 "$tmp/transcript_tests.log"
fi

echo "parity_subproof: building table_vectors"
if clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" -DBLK_FIELD=2 \
  -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o "$tmp/table_vectors" "$here/scripts/cpp_vectors/table_vectors.cpp"; then
  if "$tmp/table_vectors" "$here/fixtures/config/policy.txt" >"$tmp/table_vectors.txt"; then
    if cmp -s "$tmp/table_vectors.txt" "$here/fixtures/table_vectors.txt"; then
      ok "table_vectors: output matches fixtures/table_vectors.txt"
    else
      bad "table_vectors: output differs from fixtures/table_vectors.txt"
      diff -u "$here/fixtures/table_vectors.txt" "$tmp/table_vectors.txt" | head -20
    fi
  else
    bad "table_vectors: C++ run"
  fi
else
  bad "table_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test table_vectors \
  >"$tmp/table_vectors.log" 2>&1; then
  ok "Rust table_vectors"
else
  bad "Rust table_vectors"
  tail -30 "$tmp/table_vectors.log"
fi

echo "parity_subproof: building subproof_vectors"
if clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" -DBLK_FIELD=2 \
  -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o "$tmp/subproof_vectors" "$here/scripts/cpp_vectors/subproof_vectors.cpp"; then
  if "$tmp/subproof_vectors" >"$tmp/subproof_vectors.txt"; then
    if cmp -s "$tmp/subproof_vectors.txt" "$here/fixtures/subproof_vectors.txt"; then
      ok "subproof_vectors: output matches fixtures/subproof_vectors.txt"
    else
      bad "subproof_vectors: output differs from fixtures/subproof_vectors.txt"
      diff -u "$here/fixtures/subproof_vectors.txt" "$tmp/subproof_vectors.txt" | head -20
    fi
  else
    bad "subproof_vectors: C++ run"
  fi
else
  bad "subproof_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test subproof_vectors \
  >"$tmp/subproof_vectors.log" 2>&1; then
  ok "Rust subproof_vectors"
else
  bad "Rust subproof_vectors"
  tail -30 "$tmp/subproof_vectors.log"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test subproof_tests \
  >"$tmp/subproof_tests.log" 2>&1; then
  ok "Rust subproof_tests"
else
  bad "Rust subproof_tests"
  tail -30 "$tmp/subproof_tests.log"
fi

echo "parity_subproof: building attention_vectors"
if clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" -DBLK_FIELD=2 \
  -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o "$tmp/attention_vectors" "$here/scripts/cpp_vectors/attention_vectors.cpp"; then
  if "$tmp/attention_vectors" >"$tmp/attention_vectors.txt"; then
    if cmp -s "$tmp/attention_vectors.txt" "$here/fixtures/attention_vectors.txt"; then
      ok "attention_vectors: output matches fixtures/attention_vectors.txt"
    else
      bad "attention_vectors: output differs from fixtures/attention_vectors.txt"
      diff -u "$here/fixtures/attention_vectors.txt" "$tmp/attention_vectors.txt" | head -20
    fi
  else
    bad "attention_vectors: C++ run"
  fi
else
  bad "attention_vectors: C++ build"
fi

echo "parity_subproof: building attention_plan_vectors"
if clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" -DBLK_FIELD=2 \
  -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o "$tmp/attention_plan_vectors" "$here/scripts/cpp_vectors/attention_plan_vectors.cpp"; then
  if "$tmp/attention_plan_vectors" >"$tmp/attention_plan_vectors.txt"; then
    if cmp -s "$tmp/attention_plan_vectors.txt" "$here/fixtures/attention_plan_vectors.txt"; then
      ok "attention_plan_vectors: output matches fixtures/attention_plan_vectors.txt"
    else
      bad "attention_plan_vectors: output differs from fixtures/attention_plan_vectors.txt"
      diff -u "$here/fixtures/attention_plan_vectors.txt" "$tmp/attention_plan_vectors.txt" | head -20
    fi
  else
    bad "attention_plan_vectors: C++ run"
  fi
else
  bad "attention_plan_vectors: C++ build"
fi

for t in attention_vectors attention_plan_vectors attention_run_tests; do
  if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test "$t" \
    >"$tmp/$t.log" 2>&1; then
    ok "Rust $t"
  else
    bad "Rust $t"
    tail -30 "$tmp/$t.log"
  fi
done

echo "parity_subproof: building weights_vectors"
if clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" -DBLK_FIELD=2 \
  -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o "$tmp/weights_vectors" "$here/scripts/cpp_vectors/weights_vectors.cpp"; then
  if "$tmp/weights_vectors" >"$tmp/weights_vectors.txt"; then
    if cmp -s "$tmp/weights_vectors.txt" "$here/fixtures/weights_vectors.txt"; then
      ok "weights_vectors: output matches fixtures/weights_vectors.txt"
    else
      bad "weights_vectors: output differs from fixtures/weights_vectors.txt"
      diff -u "$here/fixtures/weights_vectors.txt" "$tmp/weights_vectors.txt" | head -20
    fi
  else
    bad "weights_vectors: C++ run"
  fi
else
  bad "weights_vectors: C++ build"
fi

for t in weights_vectors weights_tests; do
  if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test "$t" \
    >"$tmp/$t.log" 2>&1; then
    ok "Rust $t"
  else
    bad "Rust $t"
    tail -30 "$tmp/$t.log"
  fi
done

echo "parity_subproof: building layout_vectors"
if clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" -DBLK_FIELD=2 \
  -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o "$tmp/layout_vectors" "$here/scripts/cpp_vectors/layout_vectors.cpp"; then
  if "$tmp/layout_vectors" "$here/fixtures/config/policy.txt" >"$tmp/layout_vectors.txt"; then
    if cmp -s "$tmp/layout_vectors.txt" "$here/fixtures/layout_vectors.txt"; then
      ok "layout_vectors: output matches fixtures/layout_vectors.txt"
    else
      bad "layout_vectors: output differs from fixtures/layout_vectors.txt"
      diff -u "$here/fixtures/layout_vectors.txt" "$tmp/layout_vectors.txt" | head -20
    fi
  else
    bad "layout_vectors: C++ run"
  fi
else
  bad "layout_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test layout_vectors \
  >"$tmp/layout_vectors.log" 2>&1; then
  ok "Rust layout_vectors"
else
  bad "Rust layout_vectors"
  tail -30 "$tmp/layout_vectors.log"
fi

echo "parity_subproof: building context_vectors"
if clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" -DBLK_FIELD=2 \
  -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o "$tmp/context_vectors" "$here/scripts/cpp_vectors/context_vectors.cpp"; then
  if "$tmp/context_vectors" "$here/fixtures/config/policy.txt" "$here/fixtures/config/KL.bin" \
    >"$tmp/context_vectors.txt"; then
    if cmp -s "$tmp/context_vectors.txt" "$here/fixtures/context_vectors.txt"; then
      ok "context_vectors: output matches fixtures/context_vectors.txt"
    else
      bad "context_vectors: output differs from fixtures/context_vectors.txt"
      diff -u "$here/fixtures/context_vectors.txt" "$tmp/context_vectors.txt" | head -20
    fi
  else
    bad "context_vectors: C++ run"
  fi
else
  bad "context_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test context_vectors \
  >"$tmp/context_vectors.log" 2>&1; then
  ok "Rust context_vectors"
else
  bad "Rust context_vectors"
  tail -30 "$tmp/context_vectors.log"
fi

echo "parity_subproof: building req_chain_vectors"
if clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" -DBLK_FIELD=2 \
  -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o "$tmp/req_chain_vectors" "$here/scripts/cpp_vectors/req_chain_vectors.cpp"; then
  if "$tmp/req_chain_vectors" >"$tmp/req_chain_vectors.txt"; then
    if cmp -s "$tmp/req_chain_vectors.txt" "$here/fixtures/req_chain_vectors.txt"; then
      ok "req_chain_vectors: output matches fixtures/req_chain_vectors.txt"
    else
      bad "req_chain_vectors: output differs from fixtures/req_chain_vectors.txt"
      diff -u "$here/fixtures/req_chain_vectors.txt" "$tmp/req_chain_vectors.txt" | head -20
    fi
  else
    bad "req_chain_vectors: C++ run"
  fi
else
  bad "req_chain_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test req_chain_vectors \
  >"$tmp/req_chain_vectors.log" 2>&1; then
  ok "Rust req_chain_vectors"
else
  bad "Rust req_chain_vectors"
  tail -30 "$tmp/req_chain_vectors.log"
fi

echo "parity_subproof: building layers_plan_vectors"
if clang++ -O2 -std=c++17 -pthread -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" -DBLK_FIELD=2 \
  -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
  -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
  -o "$tmp/layers_plan_vectors" "$here/scripts/cpp_vectors/layers_plan_vectors.cpp"; then
  if "$tmp/layers_plan_vectors" "$here/fixtures/config/policy.txt" "$here/fixtures/config/KL.bin" \
    >"$tmp/layers_plan_vectors.txt"; then
    if cmp -s "$tmp/layers_plan_vectors.txt" "$here/fixtures/layers_plan_vectors.txt"; then
      ok "layers_plan_vectors: output matches fixtures/layers_plan_vectors.txt"
    else
      bad "layers_plan_vectors: output differs from fixtures/layers_plan_vectors.txt"
      diff -u "$here/fixtures/layers_plan_vectors.txt" "$tmp/layers_plan_vectors.txt" | head -20
    fi
  else
    bad "layers_plan_vectors: C++ run"
  fi
  if "$tmp/layers_plan_vectors" "$here/fixtures/config/policy.txt" "$here/fixtures/config/KL.bin" head \
    >"$tmp/head_plan_vectors.txt"; then
    if cmp -s "$tmp/head_plan_vectors.txt" "$here/fixtures/head_plan_vectors.txt"; then
      ok "head_plan_vectors: output matches fixtures/head_plan_vectors.txt"
    else
      bad "head_plan_vectors: output differs from fixtures/head_plan_vectors.txt"
      diff -u "$here/fixtures/head_plan_vectors.txt" "$tmp/head_plan_vectors.txt" | head -20
    fi
  else
    bad "head_plan_vectors: C++ run"
  fi
else
  bad "layers_plan_vectors: C++ build"
fi

for t in layers_plan_vectors head_plan_vectors layers_run_tests head_run_tests; do
  if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test "$t" \
    >"$tmp/$t.log" 2>&1; then
    ok "Rust $t"
  else
    bad "Rust $t"
    tail -30 "$tmp/$t.log"
  fi
done

echo "parity_subproof: cargo build --workspace"
if cargo build --manifest-path "$here/Cargo.toml" --workspace >"$tmp/build.log" 2>&1; then
  ok "cargo build --workspace"
else
  bad "cargo build --workspace"
  tail -20 "$tmp/build.log"
fi

echo "parity_subproof: cargo test --workspace"
if cargo test --manifest-path "$here/Cargo.toml" --workspace >"$tmp/test.log" 2>&1; then
  ok "cargo test --workspace"
else
  bad "cargo test --workspace"
  tail -30 "$tmp/test.log"
fi

echo "parity_subproof: fp-core no_std scan"
if grep -rnE '(^|[^A-Za-z_])use std(::|;)|extern crate std|static mut' "$here/fp-core/src" >"$tmp/scan.log"; then
  bad "fp-core holds std or a mutable static"
  cat "$tmp/scan.log"
else
  ok "fp-core: no use std, extern crate std or static mut"
fi

echo "parity_subproof: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
