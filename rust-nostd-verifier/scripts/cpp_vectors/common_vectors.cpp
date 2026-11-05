// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the verifier-reachable core of `verifier/src/vf_common.h`: the constants, the small
// helpers, the field fast paths, the equality tables and round orders, the standard parameter form
// and the acceptance policies, and the round-name mapping of `vf_transcript_channel.h`.
//
// One translation unit: `#include` `verifier/src/cp_verify.cpp` with its `main` renamed, as
// `table_vectors.cpp` does, so that the file-scope `static` helpers are callable here. The proof
// machinery is never started. Refusals are caught through `refuseThrows` (vf_common.h:52): a
// helper that would `exit(1)` throws a `Refusal` instead.
//
// Usage: common_vectors            (no arguments; the output is deterministic)
//
// Output format, one record per line, keys in lower case:
//   CONST ce=.. wpe=.. le=.. lbz=.. lbzw=.. work_bits_most=.. stage_passed_with_work=..
//         not_a_verification_status=.. withinstatus=.. field_p=<hex> field_w=..
//   TEXT <key>=<the constant's exact bytes, spaces included>
//   ORDERDEFAULT mu=<n> o=<comma-separated>
//   ORDERRANGE mu=<n> o=<comma-separated>
//   MIX64 z=<hex> m=<hex>
//   TAU tau=<n> ok=<0|1>
//   EXACT c=.. theta=.. cap=.. sh=.. st=.. ok=<0|1>
//   KIND c=.. theta=.. cap=.. s=.. sh=.. st=.. kind=<name>
//   CLIP n=.. c=.. theta=.. cap=.. sh=.. k=<n>
//   EMPTY n=.. c=.. theta=.. cap=.. sh=.. e=<n>
//   ROTARY theta0=.. dh=.. lt=.. ok=<0|1>
//   GOOD below=<0|1> notserved=<0|1> ok=<0|1>
//   VERSION v=<8 hex> ok=<0|1>
//   ADMIT i=.. v=<8 hex> ok=<0|1> fixed=<0|1> run=<8 hex>
//   LONGFILE bytes=<n> result=<ok|name>
//   INTERNAL name=<text> ok=<0|1>
//   HEX64 in=<8 words> out=<64 hex digits>
//   FINT v=<decimal> r=<hex>
//   FMAD1 a=.. x=.. y=.. r=<hex>
//   FMAD2 a=.. x1=.. y1=.. x2=.. y2=.. r=<hex>
//   FMAD3 a=.. x1=.. y1=.. x2=.. y2=.. x3=.. y3=.. r=<hex>
//   DEC arg=<text> ok=<0|1> v=<n>
//   PARSEBITS arg=<text> ok=<0|1> v=<n>
//   EQTAB len=<n> off=<n> z=<triples joined by ';'> count=<n>
//   EQTABV i=<n> v=<triple>
//   EQONE len=<n> off=<n> c=<n> z=<triples> v=<triple>
//   EQONEERR len=<n> c=<n> result=internal-eq-index
//   POLICYREAD text=<text> ok=<0|1> [kind=<name> c=.. theta=.. cap=.. s=.. sh=..]
//   SERVED mask=<hex> form=<the exact servedForm() text>
//   ROUNDNAME i=<n> name=<text>
// An `Ex` triple is three 16-digit lowercase hex words separated by commas, component 0 first.

#define main cp_verify_original_main
#include "../../verifier/src/cp_verify.cpp"
#undef main

// One Caught value says whether a call refused, and under which name.
struct Caught {
  bool refused = false;
  std::string name;
};

template <class Fn> static Caught catching(Fn fn) {
  const bool was = refuseThrows;
  refuseThrows = true;
  Caught c;
  try {
    fn();
  } catch (Refusal &r) {
    c.refused = true;
    c.name = r.name;
  }
  refuseThrows = was;
  return c;
}

static void pv(const Ex &x) {
  printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0], (unsigned long long)x.c[1],
         (unsigned long long)x.c[2]);
}

static void pz(const std::vector<Ex> &z) {
  for (size_t i = 0; i < z.size(); i++) {
    if (i) printf(";");
    pv(z[i]);
  }
}

static void ptext(const char *key, const char *value) { printf("TEXT %s=%s\n", key, value); }

static std::string join(const std::vector<int> &v) {
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    if (i) s += ",";
    s += std::to_string(v[i]);
  }
  return s;
}

// The Served fields in declaration order (vf_common.h:553-572), addressed by bit.
static Served servedFromMask(u32 m) {
  Served s;
  bool *const f[18] = {&s.experts,       &s.fiveLimbs,   &s.clamps,        &s.promptSource,
                       &s.placementTable, &s.tableDigests, &s.noRangeWords, &s.threeBytes,
                       &s.ringDegree,   &s.oneShift,    &s.onePlacement,  &s.softmaxTable,
                       &s.rotaryTable,  &s.normShifts,  &s.twoCodes,      &s.nextToken,
                       &s.exactMatch,   &s.policyNamed};
  for (int i = 0; i < 18; i++) *f[i] = ((m >> i) & 1) != 0;
  return s;
}

int main() {
  // Constants.
  printf("CONST ce=%d wpe=%llu le=%d lbz=%d lbzw=%d work_bits_most=%u stage_passed_with_work=%d "
         "not_a_verification_status=%d withinstatus=%d field_p=%016llx field_w=%llu\n",
         CE, (unsigned long long)WPE, LE, LBZ, LBZW, (unsigned)WORK_BITS_MOST,
         STAGE_PASSED_WITH_WORK_STATUS, NOT_A_VERIFICATION_STATUS, WITHINSTATUS,
         (unsigned long long)FIELD_P, (unsigned long long)FIELD_W);

  // The text constants, byte for byte.
  ptext("idline", IDLINE);
  ptext("stageidline", STAGEIDLINE);
  ptext("workline", WORKLINE);
  ptext("resultword", RESULTWORD);
  ptext("commitmentline", COMMITMENTLINE);
  ptext("one_time_line_start", ONE_TIME_LINE_START);
  ptext("recordclause", RECORDCLAUSE);
  ptext("idhidden", IDHIDDEN);
  ptext("not_a_verification_text", NOT_A_VERIFICATION_TEXT);
  ptext("within", WITHIN);
  ptext("served_layout", SERVED_LAYOUT);
  ptext("served_two_codes", SERVED_TWO_CODES);
  ptext("served_exact", SERVED_EXACT);
  ptext("served_named", SERVED_NAMED);

  // Round orders.
  for (int mu : {0, 1, 2, 5, 9}) printf("ORDERDEFAULT mu=%d o=%s\n", mu, join(orderDefault(mu)).c_str());
  for (int mu : {9, 10, 12}) printf("ORDERRANGE mu=%d o=%s\n", mu, join(orderRange(mu)).c_str());

  // The mixer.
  for (u64 z : {0ull, 1ull, 2ull, 0x9E3779B97F4A7C15ull, 0xFFFFFFFFFFFFFFFFull, 0x0123456789ABCDEFull, 42ull})
    printf("MIX64 z=%016llx m=%016llx\n", (unsigned long long)z, (unsigned long long)mix64(z));

  // tauServed, exhaustively over the admitted range's neighbourhood.
  for (u64 tau = 0; tau <= 300; tau++) printf("TAU tau=%llu ok=%d\n", (unsigned long long)tau, (int)tauServed(tau));
  for (u64 tau : {320ull, 512ull, 1024ull, 0xFFFFFFFFFFFFFFFFull})
    printf("TAU tau=%llu ok=%d\n", (unsigned long long)tau, (int)tauServed(tau));

  // acceptancePolicyIsExactMatch.
  struct Ex4 {
    u64 c, theta, cap, sh, st;
  };
  const Ex4 exact[] = {{256, 256, 0, 8, 4},       {256, 256, 0, 8, 3},       {257, 256, 0, 8, 4},
                       {256, 257, 0, 8, 4},       {256, 256, 1, 8, 4},       {256, 256, 0, 63, 59},
                       {256, 256, 0, 62, 58},     {1, 1, 0, 0, 0xFFFFFFFFFFFFFFFFull},
                       {0, 0, 0, 0, 0},           {1, 1, 0, 0, 0xFFFFFFFFFFFFFFFCull},
                       {1ull << 62, 1ull << 62, 0, 62, 58}};
  for (const Ex4 &x : exact)
    printf("EXACT c=%llu theta=%llu cap=%llu sh=%llu st=%llu ok=%d\n", (unsigned long long)x.c,
           (unsigned long long)x.theta, (unsigned long long)x.cap, (unsigned long long)x.sh,
           (unsigned long long)x.st, (int)acceptancePolicyIsExactMatch(x.c, x.theta, x.cap, x.sh, x.st));

  // policyKind.
  for (const Ex4 &x : exact)
    printf("KIND c=%llu theta=%llu cap=%llu s=%llu sh=%llu st=%llu kind=%s\n", (unsigned long long)x.c,
           (unsigned long long)x.theta, (unsigned long long)x.cap, (unsigned long long)(x.st ^ 1),
           (unsigned long long)x.sh, (unsigned long long)x.st, policyKind(x.c, x.theta, x.cap, x.st ^ 1, x.sh, x.st));
  {
    const Ex4 more[] = {{257, 256, 0, 8, 4}, {256, 256, 1, 8, 4}, {300, 299, 0, 15, 15},
                        {300, 299, 0, 15, 14}, {300, 299, 0, 4, 4}};
    for (const Ex4 &x : more)
      printf("KIND c=%llu theta=%llu cap=%llu s=%llu sh=%llu st=%llu kind=%s\n",
             (unsigned long long)x.c, (unsigned long long)x.theta, (unsigned long long)x.cap,
             (unsigned long long)x.sh, (unsigned long long)x.sh, (unsigned long long)x.st,
             policyKind(x.c, x.theta, x.cap, x.sh, x.sh, x.st));
  }

  // aboveClip.
  struct Clip {
    u64 n, c, theta, cap, sh;
  };
  const Clip clips[] = {{32, 256, 256, 0, 8},       {32, 256, 256, 64, 8},    {32, 256, 256, 31, 8},
                        {0, 256, 256, 64, 8},       {32, 100000, 40000, 64, 8}, {3, 100000, 40000, 64, 8},
                        {2, 100000, 40000, 64, 8}, {32, 100000, 40000, 3, 8}, {32, 100000000, 4000000, 0, 8},
                        {10, 300, 299, 10, 8},     {10, 300, 200, 10, 8},    {10, 200, 200, 4, 8},
                        {32, 256, 256, 0, 63},     {7, 256, 256, 100, 62}};
  for (const Clip &x : clips)
    printf("CLIP n=%llu c=%llu theta=%llu cap=%llu sh=%llu k=%llu\n", (unsigned long long)x.n,
           (unsigned long long)x.c, (unsigned long long)x.theta, (unsigned long long)x.cap,
           (unsigned long long)x.sh, (unsigned long long)aboveClip(x.n, x.c, x.theta, x.cap, x.sh));

  // policyEmpty.
  const Clip empties[] = {{1, 256, 256, 0, 8},   {0, 255, 255, 0, 8},   {0, 300, 255, 0, 8},
                          {0, 256, 257, 0, 8},   {3, 256, 256, 3, 8},   {4, 256, 256, 3, 8},
                          {0, 256, 256, 3, 8},   {500, 4096, 300, 10, 8}, {1, 128, 128, 0, 7},
                          {1, 128, 128, 0, 8},   {1, 1, 1, 0, 63},      {9, 4096, 4096, 0, 12}};
  for (const Clip &x : empties)
    printf("EMPTY n=%llu c=%llu theta=%llu cap=%llu sh=%llu e=%d\n", (unsigned long long)x.n,
           (unsigned long long)x.c, (unsigned long long)x.theta, (unsigned long long)x.cap,
           (unsigned long long)x.sh, policyEmpty(x.n, x.c, x.theta, x.cap, x.sh));

  // rotaryServed.
  struct Rot {
    u64 theta0, dh, lt;
  };
  const Rot rots[] = {{10000, 128, 10}, {500000, 128, 10}, {10001, 128, 10},
                      {10000, 129, 10}, {10000, 128, 11}, {10000, 0, 0},
                      {500000, 127, 9}};
  for (const Rot &x : rots)
    printf("ROTARY theta0=%llu dh=%llu lt=%llu ok=%d\n", (unsigned long long)x.theta0,
           (unsigned long long)x.dh, (unsigned long long)x.lt, (int)rotaryServed(x.theta0, x.dh, x.lt));

  // goodEnding.
  for (int below = 0; below < 2; below++)
    for (int ns = 0; ns < 2; ns++)
      printf("GOOD below=%d notserved=%d ok=%d\n", below, ns, (int)goodEnding(below != 0, ns != 0));

  // versionWordAdmitted on the words of the C++ negative static_assert and on this build's word.
  const u32 versions[] = {1213018161u, 1213018162u, 1212367669u, 0x48434338u, 0x48463031u,
                          0x48463032u, 2147469570u, 2147465474u, 2147461378u, 2147457282u,
                          2135734530u, 2147473666u, 1212362801u, 1212367665u, 2147408130u,
                          2147277058u, 2146228482u, 2144131330u, 2135742722u, 2118965506u,
                          1045223682u, 508352770u,  239917314u,  105699586u,  38590722u,
                          6402u,       PROGRAM_VERSION_WORD, 0u, 0xFFFFFFFFu};
  for (u32 v : versions) printf("VERSION v=%08x ok=%d\n", (unsigned)v, (int)versionWordAdmitted(v));

  // admitWord: the first admitted word sticks.
  {
    runVersionWord = 0;
    runVersionWordFixed = false;
    const u32 seq[] = {1213018161u, PROGRAM_VERSION_WORD, PROGRAM_VERSION_WORD, 1213018161u,
                       0u,           PROGRAM_VERSION_WORD};
    for (int i = 0; i < (int)(sizeof seq / sizeof seq[0]); i++) {
      const bool ok = admitWord(seq[i]);
      printf("ADMIT i=%d v=%08x ok=%d fixed=%d run=%08x\n", i, (unsigned)seq[i], (int)ok,
             (int)runVersionWordFixed, (unsigned)runVersionWord);
    }
  }

  // rejectLongTextFile.
  for (u64 bytes : {0ull, 0xFFFFFFFFull, 0x100000000ull, 0x1FFFFFFFFull}) {
    const Caught c = catching([&] { rejectLongTextFile(bytes); });
    printf("LONGFILE bytes=%llu result=%s\n", (unsigned long long)bytes, c.refused ? c.name.c_str() : "ok");
  }

  // internalName.
  const char *const names[] = {"internal-x", "internal-", "G0:internal-y", "G0:foo", "G0:", "",
                               "a:b:internal-c", "0internal-x", "internal-x:", "G:internal-",
                               "G0: internal-x", "g0:internal-x"};
  for (const char *n : names) printf("INTERNAL name=%s ok=%d\n", n, (int)internalName(n));

  // hex64.
  {
    const u32 w[DW] = {0, 1, 0xdeadbeefu, 0xFFFFFFFFu, 0, 0x12345678u, 0x9abcdef0u, 0x0badf00du};
    printf("HEX64 in=");
    for (int i = 0; i < (int)DW; i++) printf("%s%08x", i ? "," : "", (unsigned)w[i]);
    printf(" out=%s\n", hex64(w).c_str());
  }

  // fint.
  for (i64 v : {(i64)0, (i64)1, (i64)-1, (i64)7, (i64)-7, INT64_MAX, INT64_MIN, -INT64_MAX,
                (i64)-4294967295LL, (i64)4294967295LL})
    printf("FINT v=%lld r=%016llx\n", (long long)v, (unsigned long long)fint(v));

  // fmad1, fmad2, fmad3.
  struct Mad {
    u64 a, x1, y1, x2, y2, x3, y3;
  };
  const Mad mads[] = {{3, 5, 7, 11, 13, 17, 19},
                      {0xFFFFFFFFFFFFFFFFull, 0xFFFFFFFFFFFFFFFFull, 0x8000000000000000ull,
                       0x0123456789ABCDEFull, 0xFFFFFFFFFFFFFFFEull, 0xDEADBEEFCAFEBABEull,
                       0x7FFFFFFFFFFFFFFFull},
                      {0, 0, 0, 0, 0, 0, 0}};
  for (const Mad &x : mads) {
    printf("FMAD1 a=%llu x=%llu y=%llu r=%016llx\n", (unsigned long long)x.a,
           (unsigned long long)x.x1, (unsigned long long)x.y1, (unsigned long long)fmad1(x.a, x.x1, x.y1));
    printf("FMAD2 a=%llu x1=%llu y1=%llu x2=%llu y2=%llu r=%016llx\n", (unsigned long long)x.a,
           (unsigned long long)x.x1, (unsigned long long)x.y1, (unsigned long long)x.x2,
           (unsigned long long)x.y2, (unsigned long long)fmad2(x.a, x.x1, x.y1, x.x2, x.y2));
    printf("FMAD3 a=%llu x1=%llu y1=%llu x2=%llu y2=%llu x3=%llu y3=%llu r=%016llx\n",
           (unsigned long long)x.a, (unsigned long long)x.x1, (unsigned long long)x.y1,
           (unsigned long long)x.x2, (unsigned long long)x.y2, (unsigned long long)x.x3,
           (unsigned long long)x.y3, (unsigned long long)fmad3(x.a, x.x1, x.y1, x.x2, x.y2, x.x3, x.y3));
  }

  // decimal and parseRequestedBits.
  const char *const decs[] = {"0", "1", "7", "1234567", "0123", "12345678", "123456789",
                              "-1", "12a", "", "0000001", "9999999", "0000000"};
  for (const char *a : decs) {
    u32 v = 0xDEADBEEFu;
    const bool ok = decimal(a, 1000000u, v);
    printf("DEC arg=%s ok=%d v=%u\n", a, (int)ok, ok ? v : 0u);
  }
  for (const char *a : decs) {
    double v = -1;
    const bool ok = parseRequestedBits(a, v);
    printf("PARSEBITS arg=%s ok=%d v=%llu\n", a, (int)ok, ok ? (unsigned long long)v : 0ull);
  }

  // eqTab and eqOne, with the top-bit-first convention. z[0] is the top bit of the index.
  {
    const std::vector<Ex> zA = {Ex(1, 2, 3), Ex(4, 5, 6), Ex(7, 8, 9)};
    const std::vector<Ex> zB = {Ex(5, 0, 0), Ex(0, 1, 0), Ex(0, 0, 1),
                                Ex(0xFFFFFFFFFFFFFFFFull, 2, 3)};
    struct Tab {
      const std::vector<Ex> *z;
      int len;
      size_t off;
    };
    const Tab tabs[] = {{&zA, 3, 0}, {&zB, 2, 1}, {&zA, 0, 0}, {&zA, 1, 2}};
    for (const Tab &t : tabs) {
      const std::vector<Ex> v = eqTab(t.z->data() + t.off, t.len);
      printf("EQTAB len=%d off=%llu z=", t.len, (unsigned long long)t.off);
      pz(*t.z);
      printf(" count=%llu\n", (unsigned long long)v.size());
      for (size_t i = 0; i < v.size(); i++) {
        printf("EQTABV i=%llu v=", (unsigned long long)i);
        pv(v[i]);
        printf("\n");
      }
    }
    // eqOne on every index of zA, then an offset into zB.
    for (u64 c = 0; c < 8; c++) {
      const Ex x = eqOne(zA.data(), 3, c);
      printf("EQONE len=3 off=0 c=%llu z=", (unsigned long long)c);
      pz(zA);
      printf(" v=");
      pv(x);
      printf("\n");
    }
    for (u64 c = 0; c < 4; c++) {
      const Ex x = eqOne(zB.data() + 1, 2, c);
      printf("EQONE len=2 off=1 c=%llu z=", (unsigned long long)c);
      pz(zB);
      printf(" v=");
      pv(x);
      printf("\n");
    }
    struct Bad {
      int len;
      u64 c;
    };
    for (const Bad &b : {Bad{-1, 0}, Bad{64, 0}, Bad{3, 8}, Bad{63, 0x8000000000000000ull}}) {
      const Caught r = catching([&] { (void)eqOne(zA.data(), b.len, b.c); });
      printf("EQONEERR len=%d c=%llu result=%s\n", b.len, (unsigned long long)b.c,
             r.refused ? r.name.c_str() : "ok");
    }
  }

  // policyNamedRead.
  const char *const policytxt[] = {
      "exact-match,256,256,0,15,8",
      "clipped-gap,300,299,0,15,15",
      "exact-match,256,256,0,15,8,",
      "other,1,2,3,4,5",
      "exact-match,0256,256,0,15,8",
      "exact-match,12345678901,1,2,3,4",
      "exact-match,1,2,3,4",
      "exact-match,1,2,3,4,5x",
      "exact-match,1,2,3,4,5,6",
      "exact-match,1,2,3,4,5",
      "exact-match,0,0,0,0,0",
      "exact-match,00,0,0,0,0",
      ",1,2,3,4,5",
      "clipped-gap,10000000000,1,2,3,4",
      "exact-match,9999999999,9999999999,9999999999,9999999999,9999999999",
      "exact-match,",
  };
  for (const char *t : policytxt) {
    PolicyNamed p;
    const bool ok = policyNamedRead(t, p);
    printf("POLICYREAD text=%s ok=%d", t, (int)ok);
    if (ok)
      printf(" kind=%s c=%llu theta=%llu cap=%llu s=%llu sh=%llu", p.kind.c_str(),
             (unsigned long long)p.C, (unsigned long long)p.theta, (unsigned long long)p.cap,
             (unsigned long long)p.s, (unsigned long long)p.sh);
    printf("\n");
  }

  // servedForm on synthetic flag sets.
  for (u32 mask : {0u, (1u << 18) - 1u, 1u, 1u << 17, 0x2A5u, 0x15555u, 0x2AAAAu, 1u << 14})
    printf("SERVED mask=%05x form=%s\n", (unsigned)mask, servedForm(servedFromMask(mask)).c_str());

  // roundName.
  const RoundName rounds[] = {RoundName::PSC_EPSILON, RoundName::PSC_ROUND, RoundName::PSC_Y,
                              RoundName::LINE,        RoundName::ZERO,      RoundName::BAT_SIGMA,
                              RoundName::LKP,         RoundName::LKP_SHIFT, RoundName::LKP_PLANES,
                              RoundName::FOREST_POINT, RoundName::JOIN,     RoundName::PSC_VALUES};
  for (int i = 0; i < (int)(sizeof rounds / sizeof rounds[0]); i++)
    printf("ROUNDNAME i=%d name=%s\n", i, roundName(rounds[i]));
  return 0;
}
