#!/usr/bin/env bash
# Negative-control gate: the negative controls, and the cases of the two reference tests.
#
# Every case runs the C++ reference and the Rust host with the same arguments and compares, byte
# for byte, stdout (with only the stage headings' seconds normalized), stderr and the exit status.
# The expected exit status and last line of each case are also checked, and the rejection name of
# each refusal is recorded.
#
# The cases follow:
#   - verifier/tests/commitment_id_test.py: `-plan id`, `-key` under the ID, `-key` under the
#     shorter ID (the hash without the seeds and the closing word 0);
#   - verifier/tests/what_a_yes_covers_test.py, played on this repository's real-model fixtures
#     (that test's optional in-two/ and in-one/ proofs are not played: the world that carries them
#     needs the GPU prover; the test itself reports "in part" without them);
#   - the mutations: key, leaf, proof header and body, the parameter file's policy numbers,
#     KL.bin's length, and the request and y files.
#
# Usage: scripts/parity_negative.sh
#        CPP_BIN=/path/to/cp_verify scripts/parity_negative.sh

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
  echo "parity_negative: C++ reference not found; building $CPP"
  clang++ -O2 -std=c++17 -pthread \
    -I"$UPSTREAM/verifier/src" -I"$UPSTREAM/blocks" -I"$UPSTREAM/prover" \
    -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
    -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
    -o "$CPP" "$UPSTREAM/verifier/src/cp_verify.cpp" || { echo "parity_negative: C++ build failed"; exit 1; }
fi
echo "parity_negative: C++ reference: $CPP"

cargo build --manifest-path "$here/Cargo.toml" --workspace >/dev/null 2>&1 ||
  { echo "parity_negative: cargo build failed"; exit 1; }
RUST="$here/target/debug/fp-host"
[ -x "$RUST" ] || { echo "parity_negative: $RUST is missing"; exit 1; }

tmp=$(mktemp -d "${TMPDIR:-/tmp}/fp-parity-neg.XXXXXX") || exit 1
trap 'rm -rf "$tmp"' EXIT
W=$tmp/work
mkdir -p "$W" || exit 1
pass=0
fail=0
ok() { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "FAIL: $*"; }

normalize_timings() {
  sed -E 's/^(---- stage [a-z]+ ---- [0-9]+ thread\(s\), )[0-9.]+ s$/\1<T> s/' "$1"
}

CFG=$here/fixtures/config
IVK=$here/fixtures/ivk
REQ=$here/fixtures/example.req
Y=$here/fixtures/example.y
P=$here/fixtures/example.proof
ID=$(tr -d '\n' < "$here/fixtures/ID.txt")

# All case files: policy copies, request/y variants, tampered key/leaf/proof and unreadable paths.
# The mutations are deterministic recipes over the stored fixtures, like the end-to-end proof byte.
python3 -I - "$W" "$CFG" "$IVK" "$REQ" "$Y" "$P" <<'PY'
import os
import pathlib
import re
import shutil
import struct
import sys

w, cfg, ivk, req_path, y_path, proof_path = (pathlib.Path(x) for x in sys.argv[1:])

def words(b):
    return list(struct.unpack("<%dI" % (len(b) // 4), b))

def put_words(path, ws):
    pathlib.Path(path).write_bytes(struct.pack("<%dI" % len(ws), *ws))

policy = (cfg / "policy.txt").read_text()
line = dict(l.split() for l in policy.splitlines() if len(l.split()) == 2)
least = 1 << int(line["sh"])

def config(name, **numbers):
    d = w / name
    shutil.copytree(cfg, d)
    text = policy
    for name_line, value in numbers.items():
        text, times = re.subn(r"(?m)^%s \d+$" % name_line, "%s %d" % (name_line, value), text)
        assert times == 1, (name_line, times)
    (d / "policy.txt").write_text(text)

# The parameter-file copies: another policy, a kind the program does not take, and other lengths.
config("config-gap", C=least + 44, theta=least + 43)
config("config-loose", cap=1)
config("config-logprob", sT=int(line["s"]))
config("config-another", sT=int(line["sh"]) - 3)
for name, data in (("config-KLshort", (cfg / "KL.bin").read_bytes()[:20]),
                   ("config-KLodd", (cfg / "KL.bin").read_bytes() + b"\0")):
    d = w / name
    shutil.copytree(cfg, d)
    (d / "KL.bin").write_bytes(data)

# A request is T token ids, then r and e. These are the reference test's variants.
req = words(req_path.read_bytes())
reply = words(y_path.read_bytes())
T = len(req) - 2
rq = w / "req"
rq.mkdir()
put_words(rq / "wider.req", req[:T] + [T - 2, T])   # covers token T - 1 and y
put_words(rq / "prompt.req", [req[0] ^ 1] + req[1:])  # one prompt token turned
put_words(rq / "shorter.req", req[:-1])               # one word short: statement-range
put_words(rq / "longer.req", req + [0])               # one word long: statement-range
put_words(rq / "two-words.y", reply + [0])            # statement-range
(rq / "odd.req").write_bytes(req_path.read_bytes() + b"\0")   # statement-required
(rq / "empty.req").write_bytes(b"")                   # statement-required
(rq / "empty.y").write_bytes(b"")                     # statement-required
put_words(rq / "other.y", [reply[0] ^ 1])             # another reply: reply-differs

# Tampered proofs: the header's tag, its version word, and the middle word (the proof body).
pr = w / "proofs"
pr.mkdir()
for name, off in (("proof0.bin", 0), ("proof4.bin", 4)):
    b = bytearray(proof_path.read_bytes())
    b[off] ^= 1
    (pr / name).write_bytes(b)
turned = words(proof_path.read_bytes())
turned[len(turned) // 2] ^= 1
put_words(pr / "turned.bin", turned)
b = bytearray(proof_path.read_bytes())
b[2000000] ^= 1
(pr / "proofmid.bin").write_bytes(b)

# Tampered key and leaf files, under ivk folders that carry the other file unchanged.
key = (ivk / "key.bin").read_bytes()
leaf = (ivk / "leaf" / "0.bin").read_bytes()
for name, which, off in (("ivk-key0", "key", 0), ("ivk-keymid", "key", 500000),
                          ("ivk-leaf0", "leaf", 0), ("ivk-leafmid", "leaf", 500000)):
    d = w / name
    (d / "leaf").mkdir(parents=True)
    if which == "key":
        b = bytearray(key)
        b[off] ^= 1
        (d / "key.bin").write_bytes(b)
        os.symlink((ivk / "leaf" / "0.bin").resolve(), d / "leaf" / "0.bin")
    else:
        os.symlink((ivk / "key.bin").resolve(), d / "key.bin")
        b = bytearray(leaf)
        b[off] ^= 1
        (d / "leaf" / "0.bin").write_bytes(b)

# Unreadable inputs: a folder without one file, a folder where a file is named, an empty ivk.
for name, without in (("config-no-policy", "policy.txt"), ("config-no-KL", "KL.bin")):
    d = w / name
    shutil.copytree(cfg, d)
    (d / without).unlink()
d = w / "config-layout-folder"
shutil.copytree(cfg, d)
(d / "layout.txt").unlink()
(d / "layout.txt").mkdir()
(w / "no-key").mkdir()
(w / "no-key" / "leaf").mkdir()
(w / "a-folder").mkdir()
print("fixtures: made")
PY

# The shorter ID of commitment_id_test.py: the same hash without the seeds' list and the closing
# word 0 (docs/format/format_rules.py, R4.8 to R4.11).
SHORTER=$(python3 -I - "$root" "$CFG" "$IVK/key.bin" "$ID" <<'PY'
import os
import sys

root, cfg, key_path, want = sys.argv[1:]
sys.path.insert(0, os.path.join(root, "docs", "format"))
import format_rules as R  # noqa: E402

rd = lambda n: open(os.path.join(cfg, n), "rb").read()  # noqa: E731
policy, key = rd("policy.txt"), open(key_path, "rb").read()
line = {}
for x in (y.split(" ") for y in policy.decode("ascii").split("\n") if y):
    line.setdefault(x[0], x[1:])
rows, length, message, tail = (int(x) for x in line["table"][:4])
answers = int(line["answers"][0])
conf = R.configuration_digest([policy, rd("layout.txt"), rd("KL.bin")])
name = R.table_name(key[8:40], conf, length, message, tail, rows, answers, int(line["salt"][0]))
seeds = [([R.ext(x) for x in z], R.ext(beta)) for z, beta in R.record_seeds(name, (message - 1).bit_length(), answers, 2)]
stored = key[40 : 40 + 24 * (answers << rows)]
shorter = R.H(179, 0, 0, None, conf + R.string(name) + R.u64(len(stored) // 24) + stored)
mine = R.published_id(conf, name, seeds, [stored[i : i + 24] for i in range(0, len(stored), 24)]).hex()
assert mine == want, (mine, want)
print(shorter.hex())
PY
) || { echo "parity_negative: the shorter ID could not be formed"; exit 1; }
[ ${#SHORTER} -eq 64 ] || { echo "parity_negative: the shorter ID has ${#SHORTER} digits"; exit 1; }

OTHER_ID=$(printf '%s' "$ID" | tr '0123456789abcdef' '123456789abcdef0')
mkdir -p "$here/fixtures/negative"
RECORD=$here/fixtures/negative/record.tsv
: >"$tmp/names.txt"
: >"$RECORD"

# One case: <name> <expected exit> <expected last-line prefix ("-" for an empty stdout)> <argv...>.
run_case() {
  name=$1
  want=$2
  want_last=$3
  shift 3
  "$CPP" "$@" >"$tmp/cpp.out" 2>"$tmp/cpp.err"
  c=$?
  "$RUST" "$@" >"$tmp/rust.out" 2>"$tmp/rust.err"
  r=$?
  normalize_timings "$tmp/cpp.out" >"$tmp/cpp.norm"
  normalize_timings "$tmp/rust.out" >"$tmp/rust.norm"
  casefail=0
  [ "$c" -eq "$want" ] || { casefail=1; echo "  exit $c, expected $want"; }
  [ "$r" -eq "$c" ] || { casefail=1; echo "  Rust exit $r, C++ exit $c"; }
  cmp -s "$tmp/cpp.norm" "$tmp/rust.norm" ||
    { casefail=1; echo "  stdout differs"; diff -u "$tmp/cpp.norm" "$tmp/rust.norm" | head -16; }
  cmp -s "$tmp/cpp.err" "$tmp/rust.err" ||
    { casefail=1; echo "  stderr differs"; diff -u "$tmp/cpp.err" "$tmp/rust.err" | head -16; }
  last=$(tail -n 1 "$tmp/cpp.out")
  if [ "$want_last" = "-" ]; then
    [ -s "$tmp/cpp.out" ] && { casefail=1; echo "  stdout is not empty: $last"; }
  else
    case "$last" in
      "$want_last"*) ;;
      *) casefail=1; echo "  last line: $last" ;;
    esac
  fi
  recorded=${last#NO: }
  case "$last" in
    "NO: "*) printf '%s\n' "$recorded" >>"$tmp/names.txt" ;;
  esac
  { printf '%s\t%s\t%s\t' "$name" "$c" "$last"
    for a in "$@"; do
      a=${a//$W/<work>}
      a=${a//$here\/fixtures/<fixtures>}
      printf '%s ' "$a"
    done
    printf '\n'
  } >>"$RECORD"
  if [ "$casefail" -eq 0 ]; then
    ok
    printf 'PASS %s: exit %d, %s\n' "$name" "$c" "$last"
  else
    bad "$name"
  fi
}

# ---- commitment_id_test.py ----
run_case plan_id 4 "PLAN ONLY: no proof was checked" -plan id "$CFG" "$IVK/key.bin"
run_case key_named 3 "PART PASSED: key" -key "$CFG" "$IVK/key.bin" -id "$ID" -q
run_case key_shorter 1 "NO: model-statement" -key "$CFG" "$IVK/key.bin" -id "$SHORTER" -q

# ---- what_a_yes_covers_test.py (the honest fixture's own request) ----
run_case honest 0 "YES" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -q
run_case without_id 14 "NOT-A-VERIFICATION" "$CFG" "$IVK" "$REQ" "$Y" "$P" -q
run_case without_id_show 14 "NOT-A-VERIFICATION" "$CFG" "$IVK" "$REQ" "$Y" "$P" -show-stages -q
run_case other_id 1 "NO: model-statement" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$OTHER_ID" -q
run_case policy_own 0 "YES" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -policy exact-match,256,256,0,16,8 -q
run_case policy_clipped 1 "NO: policy" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -policy clipped-gap,256,256,0,16,8 -q
run_case policy_logprob 2 - "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -policy log-probability,256,256,0,16,8 -q
run_case policy_c_plus 1 "NO: policy" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -policy exact-match,257,256,0,16,8 -q
run_case policy_theta_plus 1 "NO: policy" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -policy exact-match,256,257,0,16,8 -q
run_case policy_cap_plus 1 "NO: policy" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -policy exact-match,256,256,1,16,8 -q
run_case policy_s_plus 1 "NO: policy" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -policy exact-match,256,256,0,17,8 -q
run_case policy_sh_plus 1 "NO: policy" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -policy exact-match,256,256,0,16,9 -q
run_case next_token 14 "NOT-A-VERIFICATION" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -next-token -q
run_case next_token_no_id 14 "NOT-A-VERIFICATION" "$CFG" "$IVK" "$REQ" "$Y" "$P" -next-token -q
run_case no_work 14 "NOT-A-VERIFICATION" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -no-proof-of-work -q
run_case no_work_show 14 "NOT-A-VERIFICATION" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -no-proof-of-work -show-stages -q
run_case no_work_twice 14 "NOT-A-VERIFICATION" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -no-proof-of-work -no-proof-of-work -q
run_case no_work_next 14 "NOT-A-VERIFICATION" "$CFG" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -no-proof-of-work -next-token -q
run_case no_work_no_id 14 "NOT-A-VERIFICATION" "$CFG" "$IVK" "$REQ" "$Y" "$P" -no-proof-of-work -q
run_case no_work_other_id 1 "NO: model-statement" "$CFG" "$IVK" "$REQ" "$Y" "$P" -no-proof-of-work -id "$OTHER_ID" -q
run_case no_work_other_y 1 "NO: reply-differs" "$CFG" "$IVK" "$REQ" "$W/req/other.y" "$P" -id "$ID" -no-proof-of-work -q
run_case no_work_turned 1 "NO: proof-refused" "$CFG" "$IVK" "$REQ" "$Y" "$W/proofs/turned.bin" -id "$ID" -no-proof-of-work -q
run_case wider 1 "NO: proof-refused" "$CFG" "$IVK" "$W/req/wider.req" "$Y" "$P" -id "$ID" -q
run_case prompt_turned 1 "NO: proof-refused" "$CFG" "$IVK" "$W/req/prompt.req" "$Y" "$P" -id "$ID" -q
run_case other_y 1 "NO: reply-differs" "$CFG" "$IVK" "$REQ" "$W/req/other.y" "$P" -id "$ID" -q

# ---- the parameter file sets another policy ----
run_case gap_no_policy 1 "NO: policy" "$W/config-gap" "$IVK" "$W/req/wider.req" "$Y" "$P" -id "$ID" -q
run_case gap_named 1 "NO: model-statement" "$W/config-gap" "$IVK" "$W/req/wider.req" "$Y" "$P" -id "$ID" -policy clipped-gap,300,299,0,16,8 -q
run_case gap_y_only 1 "NO: policy" "$W/config-gap" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -q
run_case loose_named 1 "NO: policy" "$W/config-loose" "$IVK" "$W/req/wider.req" "$Y" "$P" -id "$ID" -policy clipped-gap,256,256,1,16,8 -q
run_case loose_y_only 1 "NO: model-statement" "$W/config-loose" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -policy clipped-gap,256,256,1,16,8 -q
run_case kind_logprob 1 "NO: policy" "$W/config-logprob" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -q
run_case kind_another 1 "NO: policy" "$W/config-another" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -q

# ---- a request or a y of another length ----
run_case req_shorter 1 "NO: statement-range" "$CFG" "$IVK" "$W/req/shorter.req" "$Y" "$P" -id "$ID" -q
run_case req_longer 1 "NO: statement-range" "$CFG" "$IVK" "$W/req/longer.req" "$Y" "$P" -id "$ID" -q
run_case req_odd 1 "NO: statement-required" "$CFG" "$IVK" "$W/req/odd.req" "$Y" "$P" -id "$ID" -q
run_case req_empty 1 "NO: statement-required" "$CFG" "$IVK" "$W/req/empty.req" "$Y" "$P" -id "$ID" -q
run_case y_two_words 1 "NO: statement-range" "$CFG" "$IVK" "$REQ" "$W/req/two-words.y" "$P" -id "$ID" -q
run_case y_empty 1 "NO: statement-required" "$CFG" "$IVK" "$REQ" "$W/req/empty.y" "$P" -id "$ID" -q
run_case req_shorter_other_id 1 "NO: statement-range" "$CFG" "$IVK" "$W/req/shorter.req" "$Y" "$P" -id "$OTHER_ID" -q
run_case req_shorter_other_policy 1 "NO: statement-range" "$CFG" "$IVK" "$W/req/shorter.req" "$Y" "$P" -id "$ID" -policy clipped-gap,256,256,0,16,8 -q
run_case req_shorter_no_proof 1 "NO: statement-range" "$CFG" "$IVK" "$W/req/shorter.req" "$Y" "$W/none.proof" -id "$ID" -q

# ---- files that cannot be read ----
run_case no_policy 2 "input-unreadable-policy: policy.txt cannot be read: " "$W/config-no-policy" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -q
run_case no_kl 2 "input-unreadable-KL: KL.bin cannot be read: " "$W/config-no-KL" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -q
run_case layout_is_a_folder 2 "input-unreadable-layout: layout.txt cannot be read: " "$W/config-layout-folder" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -q
run_case no_key 2 "input-unreadable-key: key.bin cannot be read: " "$CFG" "$W/no-key" "$REQ" "$Y" "$P" -id "$ID" -q
run_case no_request 2 "input-unreadable-request: the request file cannot be read: " "$CFG" "$IVK" "$W/none.req" "$Y" "$P" -id "$ID" -q
run_case no_y 2 "input-unreadable-y: the y file cannot be read: " "$CFG" "$IVK" "$REQ" "$W/none.y" "$P" -id "$ID" -q
run_case no_proof 2 "input-unreadable-proof: the proof file cannot be read: " "$CFG" "$IVK" "$REQ" "$Y" "$W/none.proof" -id "$ID" -q
run_case proof_is_a_folder 2 "input-unreadable-proof: the proof file cannot be read: " "$CFG" "$IVK" "$REQ" "$Y" "$W/a-folder" -id "$ID" -q
run_case key_no_key 2 "input-unreadable-key: key.bin cannot be read: " -key "$CFG" "$W/no-key/key.bin" -q
run_case leaf_no_entry 2 "input-unreadable-entry: the entry file cannot be read: " -leaf "$CFG" "$IVK/key.bin" "$W/no-key/leaf/0.bin" -q
run_case plan_id_no_key 2 "input-unreadable-key: key.bin cannot be read: " -plan id "$CFG" "$W/no-key/key.bin"

# ---- part-calls and planning calls ----
run_case part_key 3 "PART PASSED: key" -key "$CFG" "$IVK/key.bin" -id "$ID" -q
run_case part_leaf 3 "PART PASSED: leaf" -leaf "$CFG" "$IVK/key.bin" "$IVK/leaf/0.bin" -id "$ID" -q
run_case plan_accounting 4 "PLAN ONLY: no proof was checked" -plan accounting "$CFG" 128
run_case plan_accounting_option 2 - -plan accounting "$CFG" 128 -no-proof-of-work
run_case part_key_no_work 14 "NOT-A-VERIFICATION" -key "$CFG" "$IVK/key.bin" -id "$ID" -no-proof-of-work -q
run_case part_leaf_no_work 14 "NOT-A-VERIFICATION" -leaf "$CFG" "$IVK/key.bin" "$IVK/leaf/0.bin" -id "$ID" -no-proof-of-work -q

# ---- the mutations: key, leaf, proof header and body, KL.bin's length ----
run_case key_header 1 "NO: cp-key-head" "$CFG" "$W/ivk-key0" "$REQ" "$Y" "$P" -id "$ID" -q
run_case key_middle 1 "NO: key-refused" "$CFG" "$W/ivk-keymid" "$REQ" "$Y" "$P" -id "$ID" -q
run_case leaf_header 1 "NO: entry-refused" "$CFG" "$W/ivk-leaf0" "$REQ" "$Y" "$P" -id "$ID" -q
run_case leaf_middle 1 "NO: entry-refused" "$CFG" "$W/ivk-leafmid" "$REQ" "$Y" "$P" -id "$ID" -q
run_case proof_tag 1 "NO: cp-proof-head" "$CFG" "$IVK" "$REQ" "$Y" "$W/proofs/proof0.bin" -id "$ID" -q
run_case proof_version 1 "NO: cp-proof-head" "$CFG" "$IVK" "$REQ" "$Y" "$W/proofs/proof4.bin" -id "$ID" -q
run_case proof_middle 1 "NO: proof-refused" "$CFG" "$IVK" "$REQ" "$Y" "$W/proofs/proofmid.bin" -id "$ID" -q
run_case kl_short 1 "NO: KL-length" "$W/config-KLshort" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -q
run_case kl_odd 1 "NO: KL-length" "$W/config-KLodd" "$IVK" "$REQ" "$Y" "$P" -id "$ID" -q

# ---- the rejection names that the negative controls must reach ----
required="model-statement policy statement-range statement-required proof-refused reply-differs key-refused entry-refused cp-key-head cp-proof-head KL-length"
names_all=0
names_ok=0
for n in $required; do
  names_all=$((names_all + 1))
  if grep -qx "$n" "$tmp/names.txt"; then
    names_ok=$((names_ok + 1))
  else
    bad "rejection name not reached: $n"
  fi
done

echo "parity_negative: rejection names reached:"
sort "$tmp/names.txt" | uniq -c | sed 's/^/  /'
echo "parity_negative: rejection names on the checklist: $names_ok/$names_all"
echo "parity_negative: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
