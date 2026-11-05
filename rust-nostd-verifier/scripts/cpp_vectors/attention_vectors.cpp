// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the shape of one attention sub-proof: `verifier/src/vf_attention_shape.h` and
// `aforkShapeHid()` from `verifier/src/vf_attention_check.h`.
//
// The configuration is synthetic but passes every no-overflow condition: lt = 4, lgk = 2,
// ldh = 2, la = 6, Lam = 1, S = 5, rx = 4, kFD = 10, lmS = 4, H = 8 (HA = 2), one shift (5), and
// the four calls KR, KFD, R16 and WH covering all seven lookup segments. The tool dumps the
// derived shape, the lookup calls and their tables' checksums (the 65,536-entry tables are hashed
// with mix64, and their first and last entries printed), the range check's matrices' sizes and the
// lookup forest.
//
// One translation unit: `#include` `verifier/src/cp_verify.cpp` with its `main` renamed.

#define main cp_verify_original_main
#include "../../verifier/src/cp_verify.cpp"
#undef main

#include <cinttypes>

static std::string i32s(const std::vector<int> &v) {
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    if (i) s += ",";
    s += std::to_string(v[i]);
  }
  return s;
}
static std::string u64s(const std::vector<u64> &v) {
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    if (i) s += ",";
    s += std::to_string(v[i]);
  }
  return s;
}
static std::string exs(const Ex &x) {
  char b[80];
  snprintf(b, sizeof b, "%016" PRIx64 ",%016" PRIx64 ",%016" PRIx64, (u64)eC(x, 0), (u64)eC(x, 1), (u64)eC(x, 2));
  return b;
}
static std::string vecs(const std::vector<Ex> &v) {
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    if (i) s += ";";
    s += exs(v[i]);
  }
  return s;
}
static u64 hash64(const std::vector<u64> &v) {
  u64 h = 0;
  for (u64 x : v) h = mix64(h + x);
  return h;
}

static ACfg config() {
  ACfg c;
  c.lt = 4;
  c.lB = 2;
  c.lgk = 2;
  c.ldh = 2;
  c.ll = 0;
  c.S = 5;
  c.rx = 4;
  c.kFD = 11;
  c.lmS = 4;
  c.la = 6;
  c.lmb = 11;
  c.nmin = 10;
  c.H = 8;
  c.sh = {5};
  c.wcH = 4;
  c.wcO = 4;
  c.wcQ = 8;
  c.NAs = 2;
  c.Ty = (u128)1 << (1 + LBZ);
  c.oInQa = true;
  c.lines.push_back({"KR", "KR", {sRM, sRD}});
  c.lines.push_back({"KF", "KFD", {sFM, sFD}});
  c.lines.push_back({"R", "R16", {sWL, sIX}});
  c.lines.push_back({"W", "WH", {sWH}});
  return c;
}

static void helper_vectors() {
  TenAt x{3, 2, 4, 5};
  printf("TEN off=3 nl=2 cnt=4 J=5 l=1 i=3 j=4 cell=%" PRIu64 "\n", tenCell(x, 1, 3, 4));
  std::vector<Ex> low = {eB(2), eB(3)}, tok = {eB(4), eB(5), eB(6), eB(7)};
  std::vector<Ex> br = blockRows(low, tok);
  printf("BLOCKROWS low=%s tok=%s row=%s\n", vecs(low).c_str(), vecs(tok).c_str(), vecs(br).c_str());
  for (size_t i = 0; i < br.size(); i++)
    printf("BLOCKROW i=%zu c2=%zu t=%zu idx=%zu\n", i, i / tok.size(), i % tok.size(), blockRow(i / tok.size(), i % tok.size(), tok.size()));
  std::vector<Ex> lp = longPoint(low.data(), 2, tok);
  printf("LONGPOINT p=%s\n", vecs(lp).c_str());
  std::vector<Ex> ph = longPhi(lp.data(), 2, 2);
  printf("LONGPHI p=%s\n", vecs(ph).c_str());
  std::vector<Ex> z = {eB(11), eB(12), eB(13), eB(14), eB(15)};
  PointHighLow cut = cutLast(z.data(), 5, 2);
  printf("CUT hi=%s lo=%s nhi=%d\n", vecs(std::vector<Ex>(cut.hi, cut.hi + cut.nhi)).c_str(),
         vecs(std::vector<Ex>(cut.lo, cut.lo + 2)).c_str(), cut.nhi);
  printf("LASTOF=%s\n", vecs(lastOf(z, 2)).c_str());
  for (int la = 1; la <= 3; la++) printf("HITAB la=%d want=%d v=%s\n", la, 5 - la, vecs(hiTab(z, la, 5 - la)).c_str());
  TenAt hx{0, 1, 1, 8};
  printf("HEADFEAT hd=0 dh=4 first=%" PRIu64 " hd=1 dh=4 first=%" PRIu64 "\n", headFeat(hx, 0, 4), headFeat(hx, 1, 4));
}

static void point_vectors() {
  std::vector<Ex> x = {eB(2), eB(3), eB(4)}, y = {eB(5), eB(6), eB(7)};
  printf("EQAT n=3 idx=5 v=%s\n", exs(eqAt(x.data(), 3, 5)).c_str());
  printf("EQPTS n=3 v=%s\n", exs(eqPts(x.data(), y.data(), 3)).c_str());
  printf("ONES n=3 v=%s\n", exs(onesOf(x.data(), 3)).c_str());
  printf("IDOF n=3 v=%s\n", exs(idOf(x.data(), 3)).c_str());
  printf("LEOF x<=y v=%s\n", exs(LEof(x.data(), y.data(), 3)).c_str());
  printf("LEOF y<=x v=%s\n", exs(LEof(y.data(), x.data(), 3)).c_str());
}

int main() {
  printf("CONST clamp=%d clamped=%u\n", CLAMP, CLAMPED_CELL_BOUND);
  helper_vectors();
  point_vectors();
  AFork A;
  A.cf = config();
  A.shape();
  printf("ASHAPE T=%" PRIu64 " B=%" PRIu64 " nT=%" PRIu64 " hP=%" PRIu64 " G=%" PRIu64 " HA=%" PRIu64
         " dh=%" PRIu64 " dq=%" PRIu64 " dkv=%" PRIu64 " Lam=%" PRIu64 " u0=%" PRIu64 "\n",
         A.T, A.B, A.nT, A.hP, A.G, A.HA, A.dh, A.dq, A.dkv, A.Lam, A.u0);
  printf("ASHAPE lnT=%d nM=%d nD=%d ls=%d Smax=%" PRIu64 " kAs=%" PRIu64 " kbA=%" PRIu64 "\n", A.lnT, A.nM, A.nD,
         A.ls, A.Smax, A.kAs, A.kbA);
  printf("ASHAPE featH=%" PRIu64 " featO=%" PRIu64 " featQ=%" PRIu64 " fillH=%" PRIu64 " fillO=%" PRIu64
         " fillQ=%" PRIu64 "\n",
         A.featH, A.featO, A.featQ, A.fillH, A.fillO, A.fillQ);
  printf("ASHAPE oMr=%" PRIu64 " oZr=%" PRIu64 " oIb=%" PRIu64 " oRh=%" PRIu64 " oRhp=%" PRIu64 " oQ=%" PRIu64
         " oK=%" PRIu64 " oV=%" PRIu64 " oO=%" PRIu64 "\n",
         A.oMr, A.oZr, A.oIb, A.oRh, A.oRhp, A.oQ, A.oK, A.oV, A.oO);
  printf("ASHAPE atQ=%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 " atK=%" PRIu64 ",%" PRIu64 ",%" PRIu64
         ",%" PRIu64 " atV=%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 " atO=%" PRIu64 ",%" PRIu64 ",%" PRIu64
         ",%" PRIu64 "\n",
         A.atQ.off, A.atQ.nl, A.atQ.cnt, A.atQ.J, A.atK.off, A.atK.nl, A.atK.cnt, A.atK.J, A.atV.off, A.atV.nl,
         A.atV.cnt, A.atV.J, A.atO.off, A.atO.nl, A.atO.cnt, A.atO.J);
  printf("ASHAPE tt=%zu u0=%" PRIu64 " first=%s hash=%016" PRIx64 " last=%" PRIu64 "\n", A.Tt.size(), A.u0,
         u64s(std::vector<u64>(A.Tt.begin(), A.Tt.begin() + std::min<size_t>(8, A.Tt.size()))).c_str(),
         hash64(A.Tt), A.Tt.back());
  printf("ASHAPE tableWords=%zu\n", A.tableWords());
  for (size_t q = 0; q < A.calls.size(); q++) {
    const ACall &c = A.calls[q];
    u64 th = hash64(c.tau);
    printf("ACALL q=%zu name=%s kind=%s sh=%u segs=%s n=%d k=%d kappa=%d fn=%d t0=%" PRIu64 " tot=%" PRIu64
           " pieces=%zu tauLen=%zu tauHash=%016" PRIx64,
           q, c.c.name.c_str(), c.kind.c_str(), c.sh, i32s(c.segs).c_str(), c.c.n, c.c.k, c.c.kappa, c.c.fn, c.c.t0,
           c.tot, c.pcs.size(), c.tau.size(), th);
    if (!c.tau.empty())
      printf(" tauFirst=%s tauLast=%" PRIu64, u64s(std::vector<u64>(c.tau.begin(), c.tau.begin() + std::min<size_t>(8, c.tau.size()))).c_str(), c.tau.back());
    printf("\n");
    for (size_t i = 0; i < c.pcs.size(); i++)
      printf("APIECE q=%zu i=%zu seg=%d lam=%" PRIu64 " a=%" PRIu64 " b=%d off=%" PRIu64 "\n", q, i, c.pcs[i].seg,
             c.pcs[i].lam, c.pcs[i].a, c.pcs[i].b, c.pcs[i].off);
  }
  // aforkShapeHid runs shape() again and fills the lookup forest's pub and iota.
  AFork B;
  B.cf = config();
  HForest h = aforkShapeHid(B);
  printf("AFOREST kbA=%" PRIu64 " dT=%d kT=%d NT=%d rK=%d NC=%d cK=%d iota=%s first=%s callOf=%s\n", B.kbA, h.dT, h.kT,
         h.NT, h.rK, h.NC, h.cK, i32s(h.iota).c_str(), i32s(h.first).c_str(), i32s(h.callOf).c_str());
  printf("AFOREST pub=%s padding=%" PRIu64 " elems=%zu lins=%zu\n", u64s(h.pub).c_str(), h.padding(), forestElems(h),
         forestLins(h));
  for (size_t q = 0; q < B.calls.size(); q++)
    printf("AFOREST call=%zu iota=%d n=%d\n", q, B.calls[q].c.iota, B.calls[q].c.n);
  return 0;
}
