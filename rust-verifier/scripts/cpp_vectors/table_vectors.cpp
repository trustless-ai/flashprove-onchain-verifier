// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the verifier's four public tables and their digest gate: the entries of table SILU,
// table SIG (the sigmoid, clamped when the line `gcl 1` is present), the RoPE table and the
// softmax table, each table's K(72; .) digest, the parameter file's 32 digest words, and the
// rejection name that the gate prints for a mutated digest.
//
// Sources, one translation unit: `verifier/src/cp_verify.cpp` (the static functions
// sigmoidTableEntry, sigmoidClampTableEntry and gateTableEntry at lines 181-215; the table lists at
// 1412-1428, 1592-1610 and 2004-2011; earlier_hash_h_digest) and `verifier/src/vf_attention_shape.h`
// (the softmax list, shape() lines 203-212). main() is renamed so that the included file's main is
// not the program's.
//
// Usage: table_vectors <policy.txt>
//
// Output format, deterministic and ASCII, one record per line except the entries:
//   PARAMS eg=<n> smax=<n> gcl=<0|1> ne=<n> lt=<n> dh=<n> cs=<n> theta0=<n> s=<n> rx=<n>
//   POLICY <32 words>: tsilu0..tsilu7 tsig0..tsig7 trope0..trope7 texp0..texp7, hex
//   MATCH silu=<0|1> sigmoid=<0|1> rope=<0|1> exp=<0|1>   1: the computed digest equals the line
//   MUTATION <table> <name>     the name the gate prints after flipping word 0 of that digest
//   TABLE <name> <count> <8 hex words> <digest>
//   <count entries, sixteen per line, each one 8 lowercase hex digits, single spaces>
// The table order is silu, sigmoid, rope, exp. A word is printed as the hex of its u32 value, not
// of its bytes. A model without experts (NE = 0) forms no sigmoid table and may carry no digest
// lines; this tool requires the 32 lines and NE > 0, the only form in which the gate compares all
// four digests (`cp_verify.cpp:1192-1194`, `tblHeld` at 1301-1303).

#define main cp_verify_original_main
#include "../../verifier/src/cp_verify.cpp"
#undef main

#include <fstream>
#include <iterator>

// The parameter file's bytes.
static std::string tv_slurp(const char *path) {
  std::ifstream f(path, std::ios::binary);
  if (!f) {
    fprintf(stderr, "table_vectors: cannot read %s\n", path);
    exit(2);
  }
  std::string s((std::istreambuf_iterator<char>(f)), std::istreambuf_iterator<char>());
  return s;
}

// One value line of the parameter file, read as cp_verify.cpp's polWord() reads it.
static u64 tv_word(const std::string &pol, const char *name) {
  u64 v = 0;
  if (!polWord(pol, name, v)) {
    fprintf(stderr, "table_vectors: the parameter file has no usable line %s\n", name);
    exit(2);
  }
  return v;
}

// Reads the 32 digest lines strictly, in the order that polScan() accepts (`cp_verify.cpp:1106-1118`).
// The value's spelling must pass wordLineForm(), as oneSpelling() requires.
static bool tv_digest_lines(const std::string &rest, u32 (&tbl)[4][DW]) {
  static const char *const TB[4] = {"tsilu", "tsig", "trope", "texp"};
  size_t at = 0;
  bool prev = false;
  for (size_t a = 0; a < rest.size();) {
    size_t e = rest.find('\n', a);
    if (e == std::string::npos) e = rest.size();
    const std::string line = rest.substr(a, e - a);
    const bool isTbl = !line.compare(0, 5, "tsilu") || !line.compare(0, 4, "tsig") ||
                       !line.compare(0, 5, "trope") || !line.compare(0, 4, "texp");
    if (isTbl) {
      char name[64], extra[8];
      unsigned long long val = 0;
      const std::string lf = line + "\n";
      if (at >= TBLW || (at && !prev) || sscanf(line.c_str(), "%63s %llu %7s", name, &val, extra) != 2 ||
          !wordLineForm(lf.c_str()) || val > 0xFFFFFFFFull ||
          string(TB[at / DW]) + std::to_string(at % DW) != name)
        return false;
      tbl[at / DW][at % DW] = (u32)val;
      at++;
      prev = true;
    } else {
      prev = false;
    }
    a = e + 1;
  }
  return at == TBLW;
}

static void tv_print_digest(const u32 *w) {
  for (int i = 0; i < (int)DW; i++) printf("%s%08x", i ? " " : "", (unsigned)w[i]);
}

static void tv_print_table(const char *name, const std::vector<u32> &w, const u32 *digest) {
  printf("TABLE %s %zu ", name, w.size());
  tv_print_digest(digest);
  printf("\n");
  for (size_t i = 0; i < w.size(); i += 16) {
    for (size_t j = i; j < i + 16 && j < w.size(); j++) printf("%s%08x", j == i ? "" : " ", (unsigned)w[j]);
    printf("\n");
  }
}

// The gate's comparison (`tblHeld`): a mismatch names the table.
static const char *tv_refusal(const u32 *mine, const u32 *want, const char *name) {
  return memcmp(mine, want, 4 * DW) ? name : "(none)";
}

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: %s <policy.txt>\n", argv[0]);
    return 2;
  }
  const std::string pol = tv_slurp(argv[1]);
  blk::Parameters frame;
  std::string fault;
  if (!blk::read_parameters(pol, frame, fault)) {
    fprintf(stderr, "table_vectors: %s\n", fault.c_str());
    return 2;
  }
  const u64 lt = tv_word(pol, "lt"), dh = tv_word(pol, "dh"), cs = tv_word(pol, "cs");
  const u64 theta0 = tv_word(pol, "theta0_lo") + (tv_word(pol, "theta0_hi") << 32);
  const u64 S = tv_word(pol, "S"), rx = tv_word(pol, "rx"), NE = tv_word(pol, "NE");
  if (lt < 1 || lt > 16 || !dh || (dh & 1) || cs > 31) {
    fprintf(stderr, "table_vectors: the parameter file's shape does not fit the tables\n");
    return 2;
  }
  // The optional lines that gateTableEntry() and sigmoidClampTableEntry() read, and their defaults
  // (`cp_verify.cpp:185-193`).
  u64 v = 0;
  if (polWord(pol, "eg", v)) gateTableInputFractionBits = (int)v;
  if (polWord(pol, "smax", v)) SMAX = (int)v;
  const bool gcl = polWord(pol, "gcl", v);
  if (gcl) GCL = (int)v;
  u32 tbl[4][DW] = {};
  if (!tv_digest_lines(frame.rest, tbl)) {
    fprintf(stderr, "table_vectors: the digest lines are absent, incomplete or out of order\n");
    return 2;
  }
  if (!NE) {
    fprintf(stderr, "table_vectors: NE is 0, so the file may carry no digest lines\n");
    return 2;
  }

  // Table SILU (`cp_verify.cpp:1412-1417`).
  std::vector<u32> silu(65536);
  for (int t = 0; t < 65536; t++) silu[t] = (u32)(gateTableEntry(t) + 4096);
  u32 hSilu[DW];
  earlier_hash_h_digest(hSilu, 72, silu.data(), silu.size());

  // Table SIG (`cp_verify.cpp:1422-1425`); NE > 0 here.
  std::vector<u32> sig(65536);
  for (int t = 0; t < 65536; t++) sig[t] = (u32)sigmoidClampTableEntry(t);
  u32 hSig[DW];
  earlier_hash_h_digest(hSig, 72, sig.data(), sig.size());

  // The RoPE table (`cp_verify.cpp:1592-1609`), entry by entry. l = ~0: the digest's call, whose
  // answer does not depend on a layer's rp flag.
  const u64 T = 1ull << lt;
  std::vector<u32> rope;
  rope.reserve((size_t)(2 * T * (dh / 2)));
  for (int sine = 0; sine < 2; sine++)
    for (u64 t = 0; t < T; t++)
      for (u64 i = 0; i < dh / 2; i++) {
        const double ang = (double)t * pow((double)theta0, -2.0 * (double)i / (double)dh);
        const i64 e = (i64)round((double)(1u << cs) * (sine ? sin(ang) : cos(ang)));
        rope.push_back((u32)(e + 4096));
      }
  u32 hRope[DW];
  earlier_hash_h_digest(hRope, 72, rope.data(), rope.size());

  // The softmax table (`vf_attention_shape.h:203-212`): entries while nearbyint(2^S exp(-u/2^rx)) > 0.
  std::vector<u64> tt;
  u64 u0 = 0;
  for (u64 u = 0;; u++) {
    const double x = nearbyint(ldexp(1.0, (int)S) * exp(-(double)u / ldexp(1.0, (int)rx)));
    if (x == 0) {
      u0 = u;
      break;
    }
    tt.push_back((u64)x);
    if (u > (1u << 20)) {
      fprintf(stderr, "table_vectors: the softmax table does not end\n");
      return 2;
    }
  }
  std::vector<u32> expTab;
  expTab.reserve((size_t)u0);
  for (u64 u = 0; u < u0; u++) expTab.push_back((u32)tt[u]);
  u32 hExp[DW];
  earlier_hash_h_digest(hExp, 72, expTab.data(), expTab.size());

  printf("PARAMS eg=%d smax=%d gcl=%d ne=%llu lt=%llu dh=%llu cs=%llu theta0=%llu s=%llu rx=%llu\n",
         gateTableInputFractionBits, SMAX, GCL ? 1 : 0, (unsigned long long)NE, (unsigned long long)lt,
         (unsigned long long)dh, (unsigned long long)cs, (unsigned long long)theta0, (unsigned long long)S,
         (unsigned long long)rx);
  printf("POLICY ");
  for (int k = 0; k < 4; k++)
    for (int i = 0; i < (int)DW; i++) printf("%s%08x", k || i ? " " : "", (unsigned)tbl[k][i]);
  printf("\n");
  printf("MATCH silu=%d sigmoid=%d rope=%d exp=%d\n", memcmp(hSilu, tbl[0], 4 * DW) == 0,
         memcmp(hSig, tbl[1], 4 * DW) == 0, memcmp(hRope, tbl[2], 4 * DW) == 0,
         memcmp(hExp, tbl[3], 4 * DW) == 0);
  // A mutation flips one word of the expected digest and asks for the gate's name.
  {
    static const char *const NM[4] = {"table-digest-silu", "table-digest-sigmoid", "table-digest-rope",
                                      "table-digest-exp"};
    static const char *const TB[4] = {"silu", "sigmoid", "rope", "exp"};
    const u32 *mine[4] = {hSilu, hSig, hRope, hExp};
    for (int k = 0; k < 4; k++) {
      u32 mut[DW];
      memcpy(mut, tbl[k], 4 * DW);
      mut[0] ^= 1;
      printf("MUTATION %s %s\n", TB[k], tv_refusal(mine[k], mut, NM[k]));
    }
  }
  tv_print_table("silu", silu, hSilu);
  tv_print_table("sigmoid", sig, hSig);
  tv_print_table("rope", rope, hRope);
  tv_print_table("exp", expTab, hExp);
  return 0;
}
