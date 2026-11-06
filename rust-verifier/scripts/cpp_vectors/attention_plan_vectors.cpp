// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for `AttentionSubProof::plan()` (`verifier/src/vf_attention_check.h`): the slot and
// claim counts, the range check's matrices and tree list, the lookup forest and the
// `blk::AttentionRounds` that `plan_attention_own()`/`plan_attention_end()` consume.
//
// The configuration is the synthetic one of `attention_vectors.cpp`. One translation unit:
// `#include` `verifier/src/cp_verify.cpp` with its `main` renamed.

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

int main() {
  statedTarget.hb = 0;
  AttentionSubProof sp;
  sp.A.cf = config();
  sp.A.shape();
  sp.in.gid = 1;
  sp.in.hb = 20;
  sp.in.aO = 2;
  sp.in.col0Q = 0;
  sp.in.ktO = sp.A.fillQ / sp.A.cf.wcQ;
  sp.in.midQ = 777;
  sp.in.wpS = sp.in.wph = sp.in.wpo = sp.in.wpbA = sp.in.wpq = 0;
  sp.plan();
  printf("APLAN nMsg=%zu nLin=%zu NC=%zu NP=%zu nKRp=%zu nKFp=%zu nW=%" PRIu64 " ns=%u\n", sp.nMsg, sp.nLin,
         sp.NC, sp.NP, sp.nKRp, sp.nKFp, sp.nW, sp.ns);
  printf("APLAN own lt=%u lgk=%u pairs=%u Lam=%u plane_messages=%u e=%u value_m=%u value_d=%u attained=%u bits=%u rows=%" PRIu64 "\n",
         sp.own.lt, sp.own.lgk, sp.own.pairs, sp.own.Lam, sp.own.plane_messages, sp.own.e, sp.own.value_m,
         sp.own.value_d, sp.own.attained, sp.own.bits, sp.own.rows);
  std::string score;
  for (size_t i = 0; i < sp.own.score.size(); i++) {
    if (i) score += ";";
    score += std::to_string(sp.own.score[i].first) + ":" + std::to_string(sp.own.score[i].second);
  }
  printf("APLAN score=%s\n", score.c_str());
  printf("ASEAM nU=%" PRIu64 ",%" PRIu64 ",%" PRIu64 " tabFirst=%" PRIu64 ",%" PRIu64 " tabLen=%" PRIu64 ",%" PRIu64
         " NM=%" PRIu64 " pkMat=%zu pxMat=%zu\n",
         sp.seam.nU[0], sp.seam.nU[1], sp.seam.nU[2], sp.seam.tl.tabFirst[0], sp.seam.tl.tabFirst[1],
         sp.seam.tl.tabLen[0], sp.seam.tl.tabLen[1], sp.seam.tl.NM, sp.seam.tl.pkMat.size(), sp.seam.tl.pxMat.size());
  printf("ASEAM ix U=%d,%d,%d,%d PK=%s TX=%s ZZ=%d BZ=%d FT=%s count=%d\n", sp.seam.tl.ix.U[0], sp.seam.tl.ix.U[1],
         sp.seam.tl.ix.U[2], sp.seam.tl.ix.U[3], i32s(sp.seam.tl.ix.PK).c_str(), i32s(sp.seam.tl.ix.TX).c_str(),
         sp.seam.tl.ix.ZZ, sp.seam.tl.ix.BZ, i32s(sp.seam.tl.ix.FT).c_str(), sp.seam.tl.ix.count);
  printf("ASEAM f9 dT=%d kT=%d NT=%d rK=%d NC=%d cK=%d pub=%s padding=%" PRIu64 " elems=%zu lins=%zu\n",
         sp.seam.tl.f9.dT, sp.seam.tl.f9.kT, sp.seam.tl.f9.NT, sp.seam.tl.f9.rK, sp.seam.tl.f9.NC, sp.seam.tl.f9.cK,
         u64s(sp.seam.tl.f9.pub).c_str(), sp.seam.tl.f9.padding(), sp.seam.tl.smallElems(), sp.seam.tl.lins(0));
  for (size_t mu = 0; mu < sp.seam.tl.mats.size(); mu++) {
    const TMat &m = sp.seam.tl.mats[mu];
    const ShP &s = sp.seam.tl.shp[mu];
    printf("AMAT mu=%zu name=%s m=%" PRIu64 " k=%" PRIu64 " kind=%d foreign=%d ttOff=%" PRIu64 " aId=%" PRIu64
           " wp=%u mS=%" PRIu64 " J=%" PRIu64 " R=%" PRIu64 " Rr=%" PRIu64 " Kc=%" PRIu64 "\n",
           mu, m.name.c_str(), m.m, m.k, m.kind, m.foreign, m.ttOff, m.aId, m.wp, s.mS, s.J, s.R, s.Rr, s.Kc);
  }
  for (size_t i = 0; i < sp.seam.Fp.trees.size(); i++) {
    const HTree &x = sp.seam.Fp.trees[i];
    printf("ATREE i=%zu name=%s kind=%c R=%" PRIu64 " K=%" PRIu64 " rows=%zu owner=%d\n", i, x.name.c_str(), x.kind,
           x.R, x.K, x.rows.size(), (int)x.owner);
  }
  printf("APLAN equations=%" PRIu64 " lins0=%zu\n", sp.seam.tl.equationsF(sp.seam.tl.lins(0)), sp.seam.tl.lins(0));
  return 0;
}
