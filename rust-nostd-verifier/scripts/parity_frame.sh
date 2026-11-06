#!/usr/bin/env bash
# Frame parity: the frame
#   parameters / fields / heads / req_frame / configure and the CLI-layer debts.
#
#   1. the C++ parameter-vector tool is built from the checkout's headers and compared with its
#      fixture; the Rust test replays it;
#   2. cpPolicyHeld's rejection cases are compared against the reference cp_verify, byte for byte
#      (stdout, stderr, exit status);
#   3. the whole workspace builds and its tests pass;
#   4. fp-core is scanned for `use std`, `extern crate std` and `static mut`.
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
[ -x "$CPP" ] || { echo "parity_frame: no C++ reference; set CPP_BIN"; exit 1; }

tmp=$(mktemp -d "${TMPDIR:-/tmp}/fp-frame.XXXXXX") || exit 1
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

echo "parity_frame: building frame_parameters_vectors"
if clang++ -O2 -std=c++17 -I"$UPSTREAM/blocks" -DBLK_FIELD=2 \
  -o "$tmp/frame_parameters_vectors" "$here/scripts/cpp_vectors/frame_parameters_vectors.cpp"; then
  if "$tmp/frame_parameters_vectors" "$here/fixtures/config/policy.txt" \
    >"$tmp/frame_parameters_vectors.txt"; then
    if cmp -s "$tmp/frame_parameters_vectors.txt" "$here/fixtures/frame_parameters_vectors.txt"; then
      ok "frame_parameters_vectors: vectors match fixtures/frame_parameters_vectors.txt"
    else
      bad "frame_parameters_vectors: vectors differ"
      diff -u "$here/fixtures/frame_parameters_vectors.txt" "$tmp/frame_parameters_vectors.txt" | head -20
    fi
  else
    bad "frame_parameters_vectors: C++ run"
  fi
else
  bad "frame_parameters_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test frame_parameters_vectors \
  >"$tmp/frame_parameters.log" 2>&1; then
  ok "Rust frame_parameters_vectors"
else
  bad "Rust frame_parameters_vectors"
  tail -20 "$tmp/frame_parameters.log"
fi

echo "parity_frame: building frame_layout_vectors"
if clang++ -O2 -std=c++17 -I"$UPSTREAM/blocks" -DBLK_FIELD=2 \
  -o "$tmp/frame_layout_vectors" "$here/scripts/cpp_vectors/frame_layout_vectors.cpp"; then
  if "$tmp/frame_layout_vectors" "$here/fixtures/config/layout.txt" \
    >"$tmp/frame_layout_vectors.txt"; then
    if cmp -s "$tmp/frame_layout_vectors.txt" "$here/fixtures/frame_layout_vectors.txt"; then
      ok "frame_layout_vectors: vectors match fixtures/frame_layout_vectors.txt"
    else
      bad "frame_layout_vectors: vectors differ"
      diff -u "$here/fixtures/frame_layout_vectors.txt" "$tmp/frame_layout_vectors.txt" | head -20
    fi
  else
    bad "frame_layout_vectors: C++ run"
  fi
else
  bad "frame_layout_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test frame_layout_vectors \
  >"$tmp/frame_layout.log" 2>&1; then
  ok "Rust frame_layout_vectors"
else
  bad "Rust frame_layout_vectors"
  tail -20 "$tmp/frame_layout.log"
fi

echo "parity_frame: building frame_derive_vectors"
if clang++ -O2 -std=c++17 -I"$UPSTREAM/blocks" -DBLK_FIELD=2 \
  -o "$tmp/frame_derive_vectors" "$here/scripts/cpp_vectors/frame_derive_vectors.cpp"; then
  if "$tmp/frame_derive_vectors" "$here/fixtures/config/policy.txt" \
    >"$tmp/frame_derive_vectors.txt"; then
    if cmp -s "$tmp/frame_derive_vectors.txt" "$here/fixtures/frame_derive_vectors.txt"; then
      ok "frame_derive_vectors: vectors match fixtures/frame_derive_vectors.txt"
    else
      bad "frame_derive_vectors: vectors differ"
      diff -u "$here/fixtures/frame_derive_vectors.txt" "$tmp/frame_derive_vectors.txt" | head -20
    fi
  else
    bad "frame_derive_vectors: C++ run"
  fi
else
  bad "frame_derive_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test frame_derive_vectors \
  >"$tmp/frame_derive.log" 2>&1; then
  ok "Rust frame_derive_vectors"
else
  bad "Rust frame_derive_vectors"
  tail -20 "$tmp/frame_derive.log"
fi

echo "parity_frame: building frame_wf_units_vectors"
if clang++ -O2 -std=c++17 -I"$UPSTREAM/blocks" -DBLK_FIELD=2 \
  -o "$tmp/frame_wf_units_vectors" "$here/scripts/cpp_vectors/frame_wf_units_vectors.cpp"; then
  if "$tmp/frame_wf_units_vectors" >"$tmp/frame_wf_units_vectors.txt"; then
    if cmp -s "$tmp/frame_wf_units_vectors.txt" "$here/fixtures/frame_wf_units_vectors.txt"; then
      ok "frame_wf_units_vectors: vectors match fixtures/frame_wf_units_vectors.txt"
    else
      bad "frame_wf_units_vectors: vectors differ"
      diff -u "$here/fixtures/frame_wf_units_vectors.txt" "$tmp/frame_wf_units_vectors.txt" | head -20
    fi
  else
    bad "frame_wf_units_vectors: C++ run"
  fi
else
  bad "frame_wf_units_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test frame_wf_units_vectors \
  >"$tmp/frame_wf_units.log" 2>&1; then
  ok "Rust frame_wf_units_vectors"
else
  bad "Rust frame_wf_units_vectors"
  tail -20 "$tmp/frame_wf_units.log"
fi

echo "parity_frame: building frame_wf_lines_vectors"
if clang++ -O2 -std=c++17 -I"$UPSTREAM/blocks" -DBLK_FIELD=2 \
  -o "$tmp/frame_wf_lines_vectors" "$here/scripts/cpp_vectors/frame_wf_lines_vectors.cpp"; then
  if "$tmp/frame_wf_lines_vectors" >"$tmp/frame_wf_lines_vectors.txt"; then
    if cmp -s "$tmp/frame_wf_lines_vectors.txt" "$here/fixtures/frame_wf_lines_vectors.txt"; then
      ok "frame_wf_lines_vectors: vectors match fixtures/frame_wf_lines_vectors.txt"
    else
      bad "frame_wf_lines_vectors: vectors differ"
      diff -u "$here/fixtures/frame_wf_lines_vectors.txt" "$tmp/frame_wf_lines_vectors.txt" | head -20
    fi
  else
    bad "frame_wf_lines_vectors: C++ run"
  fi
else
  bad "frame_wf_lines_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test frame_wf_lines_vectors \
  >"$tmp/frame_wf_lines.log" 2>&1; then
  ok "Rust frame_wf_lines_vectors"
else
  bad "Rust frame_wf_lines_vectors"
  tail -20 "$tmp/frame_wf_lines.log"
fi

echo "parity_frame: building plan_emitters_vectors"
if clang++ -O2 -std=c++17 -I"$UPSTREAM/blocks" -DBLK_FIELD=2 \
  -o "$tmp/plan_emitters_vectors" "$here/scripts/cpp_vectors/plan_emitters_vectors.cpp"; then
  if "$tmp/plan_emitters_vectors" >"$tmp/plan_emitters_vectors.txt"; then
    if cmp -s "$tmp/plan_emitters_vectors.txt" "$here/fixtures/plan_emitters_vectors.txt"; then
      ok "plan_emitters_vectors: vectors match fixtures/plan_emitters_vectors.txt"
    else
      bad "plan_emitters_vectors: vectors differ"
      diff -u "$here/fixtures/plan_emitters_vectors.txt" "$tmp/plan_emitters_vectors.txt" | head -20
    fi
  else
    bad "plan_emitters_vectors: C++ run"
  fi
else
  bad "plan_emitters_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test plan_emitters_vectors \
  >"$tmp/plan_emitters.log" 2>&1; then
  ok "Rust plan_emitters_vectors"
else
  bad "Rust plan_emitters_vectors"
  tail -20 "$tmp/plan_emitters.log"
fi

echo "parity_frame: building frame_sizes_vectors"
if clang++ -O2 -std=c++17 -I"$UPSTREAM/blocks" -DBLK_FIELD=2 \
  -o "$tmp/frame_sizes_vectors" "$here/scripts/cpp_vectors/frame_sizes_vectors.cpp"; then
  if "$tmp/frame_sizes_vectors" "$here/fixtures/config/policy.txt" \
    >"$tmp/frame_sizes_vectors.txt"; then
    if cmp -s "$tmp/frame_sizes_vectors.txt" "$here/fixtures/frame_sizes_vectors.txt"; then
      ok "frame_sizes_vectors: vectors match fixtures/frame_sizes_vectors.txt"
    else
      bad "frame_sizes_vectors: vectors differ"
      diff -u "$here/fixtures/frame_sizes_vectors.txt" "$tmp/frame_sizes_vectors.txt" | head -20
    fi
  else
    bad "frame_sizes_vectors: C++ run"
  fi
else
  bad "frame_sizes_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test frame_sizes_vectors \
  >"$tmp/frame_sizes.log" 2>&1; then
  ok "Rust frame_sizes_vectors"
else
  bad "Rust frame_sizes_vectors"
  tail -20 "$tmp/frame_sizes.log"
fi

echo "parity_frame: building frame_files_vectors"
if clang++ -O2 -std=c++17 -I"$UPSTREAM/blocks" -DBLK_FIELD=2 \
  -o "$tmp/frame_files_vectors" "$here/scripts/cpp_vectors/frame_files_vectors.cpp"; then
  if "$tmp/frame_files_vectors" "$here/fixtures/config/policy.txt" \
    "$here/fixtures/config-standin/policy.txt" >"$tmp/frame_files_vectors.txt"; then
    if cmp -s "$tmp/frame_files_vectors.txt" "$here/fixtures/frame_files_vectors.txt"; then
      ok "frame_files_vectors: vectors match fixtures/frame_files_vectors.txt"
    else
      bad "frame_files_vectors: vectors differ"
      diff -u "$here/fixtures/frame_files_vectors.txt" "$tmp/frame_files_vectors.txt" | head -20
    fi
  else
    bad "frame_files_vectors: C++ run"
  fi
else
  bad "frame_files_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test frame_files_vectors \
  >"$tmp/frame_files.log" 2>&1; then
  ok "Rust frame_files_vectors"
else
  bad "Rust frame_files_vectors"
  tail -20 "$tmp/frame_files.log"
fi

echo "parity_frame: building frame_configure_vectors"
if clang++ -O2 -std=c++17 -I"$UPSTREAM/blocks" -DBLK_FIELD=2 \
  -o "$tmp/frame_configure_vectors" "$here/scripts/cpp_vectors/frame_configure_vectors.cpp"; then
  if "$tmp/frame_configure_vectors" "$here/fixtures/config-standin/policy.txt" \
    >"$tmp/frame_configure_vectors.txt"; then
    if cmp -s "$tmp/frame_configure_vectors.txt" "$here/fixtures/frame_configure_vectors.txt"; then
      ok "frame_configure_vectors: vectors match fixtures/frame_configure_vectors.txt"
    else
      bad "frame_configure_vectors: vectors differ"
      diff -u "$here/fixtures/frame_configure_vectors.txt" "$tmp/frame_configure_vectors.txt" | head -20
    fi
  else
    bad "frame_configure_vectors: C++ run"
  fi
else
  bad "frame_configure_vectors: C++ build"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test frame_configure_vectors \
  >"$tmp/frame_configure.log" 2>&1; then
  ok "Rust frame_configure_vectors"
else
  bad "Rust frame_configure_vectors"
  tail -20 "$tmp/frame_configure.log"
fi

if cargo test --manifest-path "$here/Cargo.toml" -p fp-host --test frame_tree_sizes_vectors \
  >"$tmp/frame_tree_sizes.log" 2>&1; then
  ok "Rust frame_tree_sizes_vectors"
else
  bad "Rust frame_tree_sizes_vectors"
  tail -20 "$tmp/frame_tree_sizes.log"
fi

cargo build --manifest-path "$here/Cargo.toml" --workspace >/dev/null 2>&1 ||
  { echo "parity_frame: cargo build failed"; exit 1; }
RUST="$here/target/debug/fp-host"
[ -x "$RUST" ] || { echo "parity_frame: $RUST is missing"; exit 1; }

# One cpPolicyHeld case: a copy of the accepted configuration with one policy line changed and/or
# a -policy option, run against the reference. Only cases that end NO: policy are listed, because
# the Rust stages are still stubs and cannot reproduce a YES.
ID=79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183
policy_case() {
  local name=$1 old=$2 new=$3
  shift 3
  local dir="$tmp/policy-$name"
  mkdir -p "$dir"
  cp "$here/fixtures/config/"* "$dir/"
  if [ -n "$old" ]; then
    python3 -I - "$dir/policy.txt" "$old" "$new" <<'PYEOF'
import pathlib
import sys
p = pathlib.Path(sys.argv[1])
lines = p.read_text().split("\n")
hits = [i for i, line in enumerate(lines) if line == sys.argv[2]]
assert len(hits) == 1, (sys.argv[2], hits)
lines[hits[0]] = sys.argv[3]
p.write_text("\n".join(lines))
PYEOF
  fi
  "$CPP" "$dir" "$here/fixtures/ivk" "$here/fixtures/example.req" "$here/fixtures/example.y" \
    "$here/fixtures/example.proof" -id "$ID" -q "$@" >"$tmp/$name.cpp.out" 2>"$tmp/$name.cpp.err"
  local ccode=$?
  "$RUST" "$dir" "$here/fixtures/ivk" "$here/fixtures/example.req" "$here/fixtures/example.y" \
    "$here/fixtures/example.proof" -id "$ID" -q "$@" >"$tmp/$name.rust.out" 2>"$tmp/$name.rust.err"
  local rcode=$?
  if [ "$ccode" -eq 1 ] && [ "$rcode" -eq 1 ] &&
    cmp -s "$tmp/$name.cpp.out" "$tmp/$name.rust.out" &&
    cmp -s "$tmp/$name.cpp.err" "$tmp/$name.rust.err"; then
    ok "cpPolicyHeld $name"
  else
    bad "cpPolicyHeld $name (C++ $ccode, Rust $rcode)"
    diff -u "$tmp/$name.cpp.out" "$tmp/$name.rust.out" | head -12
    diff -u "$tmp/$name.cpp.err" "$tmp/$name.rust.err" | head -12
  fi
}

policy_case st5 'sT 4' 'sT 5'
policy_case c257 'C 256' 'C 257'
policy_case c128 'C 256' 'C 128'
policy_case cap3 'cap 0' 'cap 3'
policy_case named_clipped '' '' -policy clipped-gap,256,256,0,16,8
policy_case named_255 '' '' -policy exact-match,255,256,0,16,8
policy_case named_empty '' '' -policy exact-match,128,256,0,16,8

echo "parity_frame: cargo build --workspace"
if cargo build --manifest-path "$here/Cargo.toml" --workspace >"$tmp/build.log" 2>&1; then
  ok "cargo build --workspace"
else
  bad "cargo build --workspace"
  tail -20 "$tmp/build.log"
fi

echo "parity_frame: cargo test --workspace"
if cargo test --manifest-path "$here/Cargo.toml" --workspace >"$tmp/test.log" 2>&1; then
  ok "cargo test --workspace"
else
  bad "cargo test --workspace"
  tail -30 "$tmp/test.log"
fi

echo "parity_frame: fp-core no_std scan"
if grep -rnE '(^|[^A-Za-z_])use std(::|;)|extern crate std|static mut' "$here/fp-core/src" >"$tmp/scan.log"; then
  bad "fp-core holds std or a mutable static"
  cat "$tmp/scan.log"
else
  ok "fp-core: no use std, extern crate std or static mut"
fi

echo "parity_frame: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
