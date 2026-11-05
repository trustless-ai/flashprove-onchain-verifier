// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the pure parts of the norm digit rows (`verifier/src/vf_norm_digit_rows.h`) and the
// weight layout and claims (`verifier/src/vf_weights_layout.h`): the row of digits and its
// equations, the five-limb constants, the layout of W on a toy shape, `wsEpsT`, `wsRowPart`,
// `wsGammaAdd` and the merge's slot count.
//
// One translation unit: `#include` `verifier/src/cp_verify.cpp` with its `main` renamed.

#define main cp_verify_original_main
#include "../../verifier/src/cp_verify.cpp"
#undef main

#include <cinttypes>

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
static std::string u64s(const std::vector<u64> &v) {
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    if (i) s += ",";
    s += std::to_string(v[i]);
  }
  return s;
}
static u64 hash64(const std::vector<Ex> &v) {
  u64 h = 0;
  for (const Ex &x : v) {
    for (int k = 0; k < CE; k++) h = mix64(h + eC(x, k));
  }
  return h;
}

int main() {
  for (int limbs : {4, 5}) {
    residualStreamLimbs = limbs;
    printf("NORM limbs=%d ns=%d nr=%d np=%d no=%d lines=%d nrh=%d\n", limbs, ledNS(), ledNR(), ledNP(), ledNO(),
           ledLines(), ledNRH());
    std::string mu;
    for (int i = 0; i < (limbs == 5 ? 99 : 74); i++) {
      u64 m = ledMu(i);
      if (m != 1) mu += std::to_string(i) + ":" + std::to_string(m) + ";";
    }
    printf("NORM mu=%s\n", mu.c_str());
  }
  printf("NORM consts LEDNE=%d EXC=%d BIGH=%" PRIu64 " LEDG=", LEDNE, EXC, BIGH);
  for (int i = 0; i < 6; i++) printf("%s%d:%d", i ? "," : "", LEDG[i][0], LEDG[i][1]);
  printf("\n");
  {
    Row5<Ex> r = row5<Ex>([](int j) { return eB((u64)((j * 7 + 3) % 251)); });
    printf("ROW5 dg=%s\n", vecs(std::vector<Ex>(r.Dg, r.Dg + 99)).c_str());
    printf("ROW5 c=%s vlo=%s vhi=%s a=%s b=%s sig=%s s0=%s l1=%s h1=%s blo=%s bhi=%s kap=%s rlo=%s rhi=%s R=%s q1=%s rr=%s rq=%s\n",
           vecs(std::vector<Ex>(r.c, r.c + 10)).c_str(), exs(r.Vlo).c_str(), exs(r.Vhi).c_str(), exs(r.a).c_str(),
           exs(r.b).c_str(), exs(r.sig).c_str(), exs(r.s0).c_str(), exs(r.l1).c_str(), exs(r.h1).c_str(),
           exs(r.Blo).c_str(), exs(r.Bhi).c_str(), exs(r.kap).c_str(), exs(r.Rlo).c_str(), exs(r.Rhi).c_str(),
           exs(r.R).c_str(), exs(r.q1).c_str(), exs(r.rr).c_str(), exs(r.rq).c_str());
    Ex P[7];
    for (int j = 0; j < 7; j++) P[j] = eB((u64)(100 + j));
    Ex out[8];
    ledLines5<Ex>(r, P, eB(7), eB(1ull << 40), out);
    printf("LINES5 out=%s\n", vecs(std::vector<Ex>(out, out + 8)).c_str());
    Ex om[7];
    for (int j = 0; j < 7; j++) om[j] = eB((u64)(200 + j));
    printf("PRODUCTS5 v=%s\n", exs(ledProducts5(om, eB(11), eB(12), eB(13), eB(14))).c_str());
  }
  {
    WsShape s;
    s.D = 32;
    s.L = 2;
    s.d = 8;
    s.dh = 4;
    s.dkv = 6;
    s.dq = 6;
    s.f = 10;
    s.fe = 12;
    s.NE = 4;
    s.V = 11;
    s.eh = 1;
    wsSetMoe(s, true);
    std::string moe;
    for (size_t i = 0; i < s.moe.size(); i++) moe += std::to_string(s.moe[i]);
    printf("WSHAPE D=%" PRIu64 " L=%" PRIu64 " d=%" PRIu64 " dh=%" PRIu64 " dkv=%" PRIu64 " dq=%" PRIu64 " f=%" PRIu64
           " fe=%" PRIu64 " NE=%" PRIu64 " V=%" PRIu64 " eh=%u MOE=%u moe=%s\n",
           s.D, s.L, s.d, s.dh, s.dkv, s.dq, s.f, s.fe, s.NE, s.V, s.eh, s.MOE, moe.c_str());
    WsLay lay;
    lay.build(s, 6);
    printf("WSLAY lk=%d m0=%" PRIu64 " units=%zu\n", lay.lk, lay.m0, lay.U.size());
    for (size_t i = 0; i < lay.U.size(); i++) {
      const WsUnit &u = lay.U[i];
      printf("WSUNIT i=%zu X=%u l=%u nlw=%d ncb=%d rows=%" PRIu64 " off=%" PRIu64 " groups=%zu\n", i, u.X, u.l, u.nlw,
             u.ncb, u.rows, u.off, u.g.size());
      for (size_t gi = 0; gi < u.g.size(); gi++) {
        const WsGrp &g = u.g[gi];
        printf("WSGRP i=%zu gi=%zu name=%s cls=%c R=%" PRIu64 " o=%" PRIu64 " z=%d t=%d cb0=%d left=%" PRIu64
               " high=%d aTaken=%d\n",
               i, gi, g.name, g.cls, g.R, g.o, g.z, g.t, g.cb0, g.left, (int)g.high, (int)g.aTaken());
      }
    }
    // A claim on the embedding's unit (X = 12): A v (R = V) and E x (d, high).
    size_t ui = 0;
    for (size_t i = 0; i < lay.U.size(); i++)
      if (lay.U[i].X == 12) ui = i;
    WsClaim c;
    c.ui = (u32)ui;
    WsFac f0, f1;
    for (u64 i = 0; i < s.V; i++) f0.AV.push_back(eB(1000 + i));
    f1.HV.push_back(eB(3));
    f1.pt = {eB(7), eB(11), eB(13)};
    c.f = {f0, f1};
    wsClaimShape(lay, c);
    std::vector<Ex> rm;
    for (int i = 0; i < lay.lk; i++) rm.push_back(eB((u64)(20 + i)));
    Ex eps = wsEpsT(lay, c, rm);
    WsRecClaim rp = wsRowPart(lay, c, eB(17));
    printf("WSCLAIM ui=%zu eps=%s ka=%s recGroups=%zu\n", ui, exs(eps).c_str(), exs(rp.ka).c_str(), rp.f.size());
    for (size_t gi = 0; gi < rp.f.size(); gi++)
      printf("WSCLAIM gi=%zu HV=%s pl=%s AV=%s\n", gi, vecs(rp.f[gi].HV).c_str(), vecs(rp.f[gi].pl).c_str(),
             vecs(rp.f[gi].AV).c_str());
    std::vector<Ex> gam(lay.m0, eZ());
    wsGammaAdd(gam, lay, rp, eB(19));
    printf("WSGAMMA len=%zu hash=%016" PRIx64 " first=%s last=%s\n", gam.size(), hash64(gam), exs(gam[0]).c_str(),
           exs(gam.back()).c_str());
  }
  for (int lk : {1, 4, 6, 20}) printf("WSFORKSLOTS lk=%d slots=%zu\n", lk, wsForkSlots(lk));
  return 0;
}
