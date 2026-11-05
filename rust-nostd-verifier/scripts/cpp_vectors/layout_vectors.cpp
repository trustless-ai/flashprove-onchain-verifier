// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the stage layout of `verifier/src/cp_verify.cpp`: `polPrescan` / `polSkeleton` /
// `polScan` / `parseHeader` / `layout()` on the fixture parameter file. It dumps the statement's
// header (`Hdr`), the layout's sizes, tensors, weight kinds, lookup calls and forest, the RoPE
// tables' checksums and the optional lines' globals.
//
// One translation unit: `#include` `verifier/src/cp_verify.cpp` with its `main` renamed.

#define main cp_verify_original_main
#include "../../verifier/src/cp_verify.cpp"
#undef main

#include <cinttypes>
#include <fstream>
#include <iterator>

static std::string slurp(const char *path) {
  std::ifstream f(path, std::ios::binary);
  if (!f) {
    std::fprintf(stderr, "layout_vectors: cannot read %s\n", path);
    std::exit(2);
  }
  return std::string(std::istreambuf_iterator<char>(f), std::istreambuf_iterator<char>());
}
static std::string u64s(const std::vector<u64> &v) {
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    if (i) s += ",";
    s += std::to_string(v[i]);
  }
  return s;
}
static std::string i32s(const std::vector<int> &v) {
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    if (i) s += ",";
    s += std::to_string(v[i]);
  }
  return s;
}
static std::string u32s(const u32 *v, size_t n) {
  std::string s;
  for (size_t i = 0; i < n; i++) {
    if (i) s += ",";
    s += std::to_string(v[i]);
  }
  return s;
}
static std::string segs(const CallD &c) {
  std::string s;
  for (size_t i = 0; i < c.segs.size(); i++) {
    if (i) s += ";";
    s += c.segs[i].name + ":" + std::to_string(c.segs[i].n) + ":" + std::to_string((int)c.segs[i].moe);
  }
  return s;
}
static u64 hash64(const std::vector<u64> &v) {
  u64 h = 0;
  for (u64 x : v) h = mix64(h + x);
  return h;
}

int main(int argc, char **argv) {
  if (argc != 2) {
    std::fprintf(stderr, "usage: layout_vectors <policy.txt>\n");
    return 2;
  }
  const std::string pol = slurp(argv[1]);
  refuseThrows = true;
  try {
    PolScan PS;
    polPrescan(PS, pol);
    polSkeleton(PS, false);
    polScan(PS, pol);
    PS.h = parseHeader(PS.st);
    Lay y = layout(PS.h, PS.polCalls);
    const Hdr &h = PS.h;
    printf("STMT prof=%u lt=%u L=%u ll=%u d=%" PRIu64 " H=%" PRIu64 " Gk=%" PRIu64 " dh=%" PRIu64 " f=%" PRIu64
           " fe=%" PRIu64 " NE=%" PRIu64 " V=%" PRIu64 " eps=%" PRIu64 ",%" PRIu64 " cs=%u theta0=%" PRIu64
           " la=%u nmin=%u D=%" PRIu64 " tau=%u\n",
           h.prof, h.lt, h.L, h.ll, h.d, h.H, h.Gk, h.dh, h.f, h.fe, h.NE, h.V, h.eps[0], h.eps[1], h.cs,
           h.theta0, h.la, h.nmin, h.D, h.tau);
    printf("STMT hf=%s ut=%u\n", u32s(h.hf, 13).c_str(), h.ut);
    printf("STMT lmaf=%u NAf=%u lmad=%u NAd=%u lmar=%u lmb=%u lmq=%u lmx=%u\n", h.lmaf, h.NAf, h.lmad, h.NAd, h.lmar,
           h.lmb, h.lmq, h.lmx);
    printf("STMT wb=%s iota=%s\n", u32s(h.wb, 12).c_str(), u32s(h.iota, 8).c_str());
    printf("STMT lB=%u S=%u rx=%u kFM=%u kFD=%u lmS=%u NAs=%u lmh=%u lmo=%u lmbA=%u iotaA0=%u\n", h.lB, h.Sx, h.rx,
           h.kFM, h.kFD, h.lmS, h.NAs, h.lmh, h.lmo, h.lmbA, h.iotaA0);
    printf("STMT MF=%u KF=%u epsF=%" PRIu64 " toksrc=%u lmhf=%u NHf=%u lmhd=%u lmhr=%u lmbH=%u wbH=%s iotaH=%s\n",
           h.MF, h.KF, h.epsF, h.toksrc, h.lmhf, h.NHf, h.lmhd, h.lmhr, h.lmbH, u32s(h.wbH, 2).c_str(),
           u32s(h.iotaH, 6).c_str());
    printf("STMT C=%u theta=%u cap=%u s=%u sh=%u sT=%u F=%u yTok=%u\n", h.clipC, h.theta, h.cap, h.logS, h.digSh,
           h.tabS, h.famF, h.yTok);
    printf("STMT target at=%zu hb=%u\n", statedTarget.at, statedTarget.hb);
    printf("OPT lidb=%d nminh=%d rcl=%d gcl=%d limbs=%d pow=%d pows=%d powc=%d eg=%d smax=%d\n", LIDB, NMINH, RCL,
           GCL, residualStreamLimbs, POW, POWS, POWC, gateTableInputFractionBits, SMAX);
    printf("LAY T=%" PRIu64 " Lam=%" PRIu64 " NGr=%" PRIu64 " Pd=%" PRIu64 " Pf=%" PRIu64 " S2=%" PRIu64
           " NW=%" PRIu64 " NN=%" PRIu64 " NI=%" PRIu64 " dq=%" PRIu64 " dkv=%" PRIu64 " nqk=%" PRIu64
           " lPf=%d lfe=%d lPd=%d ls=%d ldh=%d LamM=%" PRIu64 " lNE=%d kbm=%" PRIu64 "\n",
           y.T, y.Lam, y.NGr, y.Pd, y.Pf, y.S2, y.NW, y.NN, y.NI, y.dq, y.dkv, y.nqk, y.lPf, y.lfe, y.lPd, y.ls,
           y.ldh, y.LamM, y.lNE, y.kbm);
    printf("LAY arrays feat=%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 " filled=%" PRIu64 ",%" PRIu64 ",%" PRIu64
           ",%" PRIu64 " kcol=%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 " mrow=%" PRIu64 ",%" PRIu64 ",%" PRIu64
           ",%" PRIu64 " parts=%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 "\n",
           y.feat[0], y.feat[1], y.feat[2], y.feat[3], y.filled[0], y.filled[1], y.filled[2], y.filled[3], y.kcol[0],
           y.kcol[1], y.kcol[2], y.kcol[3], y.mrow[0], y.mrow[1], y.mrow[2], y.mrow[3], y.parts[0], y.parts[1],
           y.parts[2], y.parts[3]);
    printf("LAY xb xbFilled=%" PRIu64 " kxb=%" PRIu64 " mxb=%" PRIu64 " off=%" PRIu64 " nl=%" PRIu64 " cnt=%" PRIu64
           " J=%" PRIu64 "\n",
           y.xbFilled, y.kxb, y.mxb, y.xb.off, y.xb.nl, y.xb.cnt, y.xb.J);
    for (size_t i = 0; i < y.ten.size(); i++) {
      const Ten &t = y.ten[i];
      printf("TEN i=%zu name=%s mat=%d nl=%d cnt=%" PRIu64 " J=%" PRIu64 " OFF=%" PRIu64 "\n", i, t.name.c_str(),
             t.mat, t.nl, t.cnt, t.J, t.OFF);
    }
    for (size_t i = 0; i < y.kinds.size(); i++)
      printf("KIND i=%zu idx=%d name=%s L=%" PRIu64 " segs=%" PRIu64 "\n", i, y.kinds[i].idx, y.kinds[i].name.c_str(),
             y.kinds[i].L, y.kinds[i].segs);
    printf("TAU fc=%016" PRIx64 " fl=%016" PRIx64 " fs=%016" PRIx64 " lens=%zu,%zu,%zu\n", hash64(y.tauFC),
           hash64(y.tauFL), hash64(y.tauFS), y.tauFC.size(), y.tauFL.size(), y.tauFS.size());
    for (size_t q = 0; q < y.calls.size(); q++) {
      const CallD &c = y.calls[q];
      printf("CALL q=%zu name=%s kind=%s n=%d iota=%d kappa=%d k=%d fn=%d t0=%" PRIu64 " lJ=%d J=%" PRIu64
             " segs=%s\n",
             q, c.c.name.c_str(), c.kind.c_str(), c.c.n, c.c.iota, c.c.kappa, c.c.k, c.c.fn, c.c.t0, c.lJ, c.J,
             segs(c).c_str());
      std::string used;
      for (size_t j = 0; j < c.used.size(); j++) used += std::to_string((int)c.used[j]);
      printf("CALL used q=%zu used=%s\n", q, used.c_str());
    }
    const HForest &fo = y.fo;
    printf("FOREST dT=%d kT=%d NT=%d rK=%d NC=%d cK=%d iota=%s first=%s callOf=%s\n", fo.dT, fo.kT, fo.NT, fo.rK,
           fo.NC, fo.cK, i32s(fo.iota).c_str(), i32s(fo.first).c_str(), i32s(fo.callOf).c_str());
    printf("FOREST pub=%s padding=%" PRIu64 " elems=%zu lins=%zu\n", u64s(fo.pub).c_str(), fo.padding(),
           forestElems(fo), forestLins(fo));
  } catch (Refusal &r) {
    printf("REFUSED %s\n", r.name.c_str());
    return 1;
  }
  return 0;
}
