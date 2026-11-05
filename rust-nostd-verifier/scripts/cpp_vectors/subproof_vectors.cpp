// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the instantiable parts of the sub-proof machinery:
//   verifier/src/vf_subproof_engine.h    (powerOfTwoAtLeast, Aff, HFork slots/hide/push/settle,
//                                         kapAt/kapTake)
//   verifier/src/vf_smallness_packing.h  (placeP, tieLeft, tieRight, samePlaceF)
//   verifier/src/vf_smallness_matrices.h (TMat, Tail)
//   verifier/src/vf_smallness_test.h     (shapeF, piecesF, addTreesF, lins, equations)
//   verifier/src/vf_lookup_helpers.h     (placeZ, uEnt, HFun)
//   verifier/src/vf_lookup_argument.h    (forestShape, forestPubRun, forestPubAsk, forestElems,
//                                         forestLins, orderForestRange, padKey, emptyKeys, padding)
//   verifier/src/vf_sumcheck_psc.h       (pscRow with a hand-built Psc)
//   verifier/src/vf_sumcheck_receive.h   (roundValues, sumcheckSlots, layerSlots)
//   verifier/src/vf_sumcheck_token.h     (tscSlots)
//   verifier/src/vf_sumcheck_attention.h (sc3Slots)
//
// The transcript-driven calls (pscBegin, roundIn, pscEnds, forestPad, transcriptF, ...) need a
// `Tr` on a real chain; they are exercised by fp-host/tests/subproof_tests.rs on the Rust side.
//
// One translation unit: `#include` `verifier/src/cp_verify.cpp` with its `main` renamed, as
// `table_vectors.cpp` does. Refusals are caught through `refuseThrows`. The program is
// deterministic and writes one record per line.

#define main cp_verify_original_main
#include "../../verifier/src/cp_verify.cpp"
#undef main

#include <cinttypes>

struct Caught {
  bool refused = false;
  std::string name;
};

template <class Fn> static Caught catching(Fn fn) {
  const bool was = refuseThrows;
  refuseThrows = true;
  try {
    fn();
  } catch (Refusal &r) {
    refuseThrows = was;
    return {true, r.name};
  }
  refuseThrows = was;
  return {};
}

static std::string exs(const Ex &x) {
  char b[80];
  snprintf(b, sizeof b, "%016" PRIx64 ",%016" PRIx64 ",%016" PRIx64, (u64)eC(x, 0), (u64)eC(x, 1), (u64)eC(x, 2));
  return b;
}
static std::string affs(const Aff &a) {
  std::string s = "c=" + exs(a.c) + " e=";
  for (size_t i = 0; i < a.e.size(); i++) {
    const Ent &x = a.e[i];
    if (i) s += ";";
    s += std::to_string(x.tree) + ":" + std::to_string(x.row) + ":" + std::to_string(x.idx) + ":" + exs(x.coef);
  }
  s += " s=";
  for (size_t i = 0; i < a.s.size(); i++) {
    if (i) s += ";";
    s += std::to_string(a.s[i].first) + ":" + exs(a.s[i].second);
  }
  return s;
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
static std::string i32s(const std::vector<int> &v) {
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    if (i) s += ",";
    s += std::to_string(v[i]);
  }
  return s;
}

static void power_of_two() {
  const u64 vs[] = {0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, (1ull << 20), (1ull << 32) - 1, 1ull << 32, 1ull << 63};
  for (u64 v : vs) printf("POW2 v=%" PRIu64 " p=%" PRIu64 "\n", v, powerOfTwoAtLeast(v));
}

static void aff_vectors() {
  Aff a = affC(eB(11));
  affAdd(a, affSlot(2), eB(3));
  affAdd(a, affEnt(1, 2, 7), eB(5));
  Aff b = affSlot(4) * eB(9);
  affAdd(b, affC(eB(13)), eB(2));
  printf("AFF a=%s\n", affs(a).c_str());
  printf("AFF b=%s\n", affs(b).c_str());
  printf("AFF sum=%s\n", affs(a + b).c_str());
  printf("AFF diff=%s\n", affs(a - b).c_str());
  printf("AFF scaled=%s\n", affs(a * eB(7)).c_str());
}

static HFork basic_fork() {
  HFork f;
  f.G_ = "t:";
  f.slots(8);
  return f;
}

static void fork_vectors() {
  {
    HFork f = basic_fork();
    f.hide(0, eB(5), eB(2));
    f.hide(1, eB(7), eB(3));
    f.LS[0] = eB(4);
    f.LS[1] = eB(9);
    f.c0 = eB(11);
    std::vector<Ex> mask;
    Ex c0;
    f.settle(mask, c0, 2);
    printf("SETTLE ok mask=%s c=%s\n", vecs(mask).c_str(), exs(c0).c_str());
  }
  {
    HFork f = basic_fork();
    f.hide(0, eB(5), eB(2));
    f.LS[1] = eB(9);
    std::vector<Ex> mask;
    Ex c0;
    Caught c = catching([&] { f.settle(mask, c0, 2); });
    printf("SETTLE missing slot result=%s\n", c.refused ? c.name.c_str() : "ok");
  }
  {
    HFork f = basic_fork();
    Caught c = catching([&] { f.hide(0, eB(5), eB(2)), f.hide(0, eB(6), eB(3)); });
    printf("HIDE twice result=%s\n", c.refused ? c.name.c_str() : "ok");
  }
  {
    HFork f = basic_fork();
    f.batchBy(eB(3));
    printf("KAP c0=%s c1=%s c2=%s c5=%s\n", exs(f.kapAt(0)).c_str(), exs(f.kapAt(1)).c_str(),
           exs(f.kapAt(2)).c_str(), exs(f.kapAt(5)).c_str());
    f.planClaimsF = 6;
    f.kapMapF.assign(6, 0);
    f.kapTake(2);
    Caught c = catching([&] { f.kapTake(2); });
    printf("KAP twice result=%s\n", c.refused ? c.name.c_str() : "ok");
    Caught d = catching([&] { f.kapTake(6); });
    printf("KAP high result=%s\n", d.refused ? d.name.c_str() : "ok");
  }
  {
    HFork f = basic_fork();
    HTree x;
    x.name = "A", x.kind = 'N', x.R = 4, x.K = 3;
    x.rows.resize(1);
    x.rows[0].L0 = 1;
    x.rows[0].L.assign(3, eZ());
    f.trees.push_back(x);
    Aff a;
    affAdd(a, affEnt(0, 0, 3), eB(2));
    f.push(eB(5), a);
    printf("PUSH L=%s c0=%s\n", vecs(f.trees[0].rows[0].L).c_str(), exs(f.c0).c_str());
    Aff bad;
    affAdd(bad, affEnt(0, 0, 0), eO());
    Caught c = catching([&] { f.push(eO(), bad); });
    printf("PUSH low result=%s\n", c.refused ? c.name.c_str() : "ok");
  }
  {
    HFork f = basic_fork();
    HTree x;
    x.name = "T", x.kind = 'N', x.R = 4, x.K = 5;
    x.rows.resize(1);
    f.trees.push_back(x);
    for (u64 v : {0ull, 1ull, 4ull, 5ull, 19ull, 20ull}) {
      Aff a = uEnt(f, 0, v);
      printf("UENT x=%" PRIu64 " %s\n", v, affs(a).c_str());
    }
    Caught c = catching([&] { uEnt(f, 0, (1ull << 32) * 5); });
    printf("UENT high result=%s\n", c.refused ? c.name.c_str() : "ok");
  }
}

static void packing_vectors() {
  ShP s;
  s.m = 10;
  s.k = 5;
  s.mS = 4;
  s.J = 1;
  s.cJ = 0;
  s.R = s.Rr = 4;
  s.Rd = 0;
  s.aX = 2;
  s.K1 = s.Kc = 5;
  s.a = 1;
  std::vector<Ex> rows = {eB(3), eB(4), eB(5), eB(6)}, lo = {eB(2)}, gam = {eB(100), eB(101), eB(102), eB(103), eB(104)};
  std::vector<Ex> wl = tieLeft(s, rows, lo), wr = tieRight(s, lo, gam);
  printf("SHAPE m=%" PRIu64 " k=%" PRIu64 " mS=%" PRIu64 " J=%" PRIu64 " R=%" PRIu64 " Rr=%" PRIu64 " K1=%" PRIu64
         " Kc=%" PRIu64 " aX=%d\n",
         s.m, s.k, s.mS, s.J, s.R, s.Rr, s.K1, s.Kc, s.aX);
  for (u64 i = 0; i < 4; i++) {
    PlP p = placeP(s, i, 3);
    printf("PLACE iS=%" PRIu64 " c=3 row=%" PRIu64 " place=%" PRIu64 "\n", i, p.row, p.place);
  }
  printf("TIE left=%s\n", vecs(wl).c_str());
  printf("TIE right=%s\n", vecs(wr).c_str());
  std::vector<Ex> ez = {eB(2), eB(3), eB(4)};
  printf("EQPLAIN n=3 idx=5 z=%s v=%s\n", vecs(ez).c_str(), exs(eqPlainF(ez.data(), 3, 5)).c_str());
  UnscaledEqIterator it(ez.data(), 3, 5);
  for (int i = 0; i < 4; i++, it.next()) printf("UNSCALED i=%d v=%s\n", i, exs(it.at()).c_str());
  PlaceF o, r;
  o.owner = r.owner = 0;
  o.sh = r.sh = s;
  o.col0 = r.col0 = 0;
  o.k = r.k = 5;
  o.K = r.K = 5;
  o.m = r.m = 10;
  o.rootIndex = r.rootIndex = 0;
  o.hb = r.hb = 1;
  o.mS = r.mS = 4;
  o.lanes = r.lanes = 3;
  o.padRows = r.padRows = 4;
  o.J = r.J = 1;
  o.off = r.off = 0;
  o.w = r.w = 0;
  printf("SAMEPLACE equal='%s'\n", samePlaceF(o, r));
  r.owner = 1;
  printf("SAMEPLACE owner='%s'\n", samePlaceF(o, r));
  r.owner = 0;
  r.hb = 2;
  printf("SAMEPLACE hb='%s'\n", samePlaceF(o, r));
}

static void forest_vectors() {
  Call a, b;
  a.name = "A", a.n = 22, a.k = 6, a.kappa = 5, a.fn = 0, a.t0 = 0;
  b.name = "B", b.n = 20, b.k = 5, b.kappa = 5, b.fn = 0, b.t0 = 3;
  std::vector<Call *> cl = {&a, &b};
  HForest h = forestShape(cl, 22);
  printf("FOREST dT=%d kT=%d NT=%d rK=%d NC=%d cK=%d v=%d d=%d\n", h.dT, h.kT, h.NT, h.rK, h.NC, h.cK, h.v(), h.d());
  printf("FOREST iota=%s first=%s callOf=%s empty=%" PRIu64 "\n", i32s(h.iota).c_str(), i32s(h.first).c_str(),
         i32s(h.callOf).c_str(), h.emptyKeys());
  printf("FOREST padKey0=%s padKey1=%s\n", exs(h.padKey(0)).c_str(), exs(h.padKey(1)).c_str());
  std::vector<u64> pub(h.NT, 0);
  forestPubRun(h, pub, 0, 0, 3);
  forestPubRun(h, pub, 0, 5, 2);
  forestPubRun(h, pub, 1, 0, 4);
  forestPubRun(h, pub, 1, 7, 1);
  printf("FOREST pub=%s padding=%" PRIu64 "\n", u64s(pub).c_str(), [&] {
    HForest q = h;
    q.pub = pub;
    return q.padding();
  }());
  forestPubAsk(h, cl, pub);
  printf("FOREST elems=%zu lins=%zu planeCols5=%" PRIu64 " planeCols11=%" PRIu64 "\n", forestElems(h), forestLins(h),
         forestPlaneCols(h, 5), forestPlaneCols(h, 11));
  printf("FOREST orderRange=%s\n", i32s(orderForestRange(23, 3)).c_str());
  {
    std::vector<u64> bad = pub;
    bad[0] = (1ull << h.dT) + 1;
    Caught c = catching([&] { forestPubAsk(h, cl, bad); });
    printf("FOREST pubAsk high result=%s\n", c.refused ? c.name.c_str() : "ok");
  }
  {
    // A call that is all padding: tree 0 of call 1.
    std::vector<u64> only = pub;
    only[4] = 1ull << h.dT;
    only[0] = only[1] = only[2] = 0;
    Caught c = catching([&] { forestPubAsk(h, cl, only); });
    printf("FOREST pubAsk all-padding result=%s\n", c.refused ? c.name.c_str() : "ok");
  }
}

static void placez_vectors() {
  HCallZ z;
  HPiece p0, p1;
  p0.tree = 0, p0.row = 0, p0.r0 = 0, p0.Rp = 3, p0.c0 = 0, p0.Cp = 5;
  p1.tree = 0, p1.row = 1, p1.r0 = 0, p1.Rp = 1, p1.c0 = 0, p1.Cp = 1;
  z.pc = {p0, p1};
  placeZ(z, "R10z", 10, 22);
  printf("PLACEZ name=%s n=%d iota=%d k=%d kappa=%d fn=%d t0=%" PRIu64 " pub=%s\n", z.c.name.c_str(), z.c.n, z.c.iota,
         z.c.k, z.c.kappa, z.c.fn, z.c.t0, u64s(z.c.pub).c_str());
  for (size_t i = 0; i < z.pc.size(); i++)
    printf("PLACEZ piece=%zu a=%d b=%d CP=%" PRIu64 " off=%" PRIu64 "\n", i, z.pc[i].a, z.pc[i].b, z.pc[i].CP,
           z.pc[i].off);
}

static void block_vectors() {
  for (u64 r : {160ull, 5ull, 32ull, 33ull, 256ull}) {
    std::vector<std::pair<u64, u64>> b = t2BL(r);
    std::string s;
    for (size_t i = 0; i < b.size(); i++) {
      if (i) s += ",";
      s += "(" + std::to_string(b[i].first) + "," + std::to_string(b[i].second) + ")";
    }
    printf("T2BL r=%" PRIu64 " blocks=%s\n", r, s.c_str());
  }
}

static void smallness_shape_vectors() {
  TMat m0;
  m0.name = "qa", m0.m = 10, m0.k = 5, m0.kind = 0, m0.wp = 0;
  std::vector<TMat> mats = {m0};
  std::vector<int> txOf = {-1};
  std::vector<T2Foreign> ft;
  bool hasU[4] = {true, true, true, false};
  HTailF2 T;
  T.shape(mats, txOf, ft, hasU, T2TAU);
  printf("TAIL mz=%" PRIu64 " NM=%" PRIu64 " off=%s col0=%s gtTree=%s gtRow=%s\n", T.mz, T.NM, u64s(T.off).c_str(),
         u64s(T.col0).c_str(), i32s(std::vector<int>(T.gtTree.begin(), T.gtTree.end())).c_str(),
         i32s(std::vector<int>(T.gtRow.begin(), T.gtRow.end())).c_str());
  printf("TAIL ix U=%d,%d,%d,%d PK=%s TX=%s ZZ=%d BZ=%d FT=%s count=%d\n", T.ix.U[0], T.ix.U[1], T.ix.U[2], T.ix.U[3],
         i32s(T.ix.PK).c_str(), i32s(T.ix.TX).c_str(), T.ix.ZZ, T.ix.BZ, i32s(T.ix.FT).c_str(), T.ix.count);
  printf("TAIL lins0=%zu lins3=%zu elems=%zu bzCols=%" PRIu64 " eq0=%" PRIu64 " eq3=%" PRIu64 "\n", T.lins(0),
         T.lins(3), T.smallElems(), T.bzColumns(), T.equationsF(0), T.equationsF(3));
  for (int q = 1; q <= 2; q++) {
    printf("TAIL call%d name=%s n=%d iota=%d k=%d kappa=%d pub=%s pieces=%zu\n", q, T.z[q].c.name.c_str(), T.z[q].c.n,
           T.z[q].c.iota, T.z[q].c.k, T.z[q].c.kappa, u64s(T.z[q].c.pub).c_str(), T.z[q].pc.size());
    for (size_t i = 0; i < T.z[q].pc.size(); i++)
      printf("TAIL call%d piece=%zu tree=%d row=%d r0=%" PRIu64 " Rp=%" PRIu64 " c0=%" PRIu64 " Cp=%" PRIu64
             " CP=%" PRIu64 " off=%" PRIu64 " a=%d b=%d\n",
             q, i, T.z[q].pc[i].tree, T.z[q].pc[i].row, T.z[q].pc[i].r0, T.z[q].pc[i].Rp, T.z[q].pc[i].c0,
             T.z[q].pc[i].Cp, T.z[q].pc[i].CP, T.z[q].pc[i].off, T.z[q].pc[i].a, T.z[q].pc[i].b);
  }
  printf("TAIL f9 dT=%d kT=%d NT=%d rK=%d NC=%d cK=%d pub=%s padding=%" PRIu64 "\n", T.f9.dT, T.f9.kT, T.f9.NT,
         T.f9.rK, T.f9.NC, T.f9.cK, u64s(T.f9.pub).c_str(), T.f9.padding());
  HFork f;
  f.G_ = "t:";
  Tail2 tail;
  u64 nU[3] = {1, 1, 37};
  std::vector<u32> aTX;
  statedTarget.hb = 0;
  T.addTrees(f, tail, nU, aTX, 1);
  printf("TAIL tabFirst=%" PRIu64 ",%" PRIu64 " tabLen=%" PRIu64 ",%" PRIu64 "\n", T.tabFirst[0], T.tabFirst[1],
         T.tabLen[0], T.tabLen[1]);
  for (size_t i = 0; i < f.trees.size(); i++) {
    const HTree &x = f.trees[i];
    printf("TAIL tree=%zu name=%s kind=%c R=%" PRIu64 " K=%" PRIu64 " rows=%zu owner=%d\n", i, x.name.c_str(), x.kind,
           x.R, x.K, x.rows.size(), (int)x.owner);
  }
  for (size_t mu = 0; mu < T.NM; mu++) {
    const ShP &s = T.shp[mu];
    printf("TAIL shp mu=%zu m=%" PRIu64 " k=%" PRIu64 " mS=%" PRIu64 " w=%d ln=%d cJ=%d aX=%d t=%u a=%u n=%" PRIu64
           " mk=%" PRIu64 " P2=%" PRIu64 " K1=%" PRIu64 " Kc=%" PRIu64 " J=%" PRIu64 " R=%" PRIu64 " Rd=%" PRIu64
           " Rr=%" PRIu64 "\n",
           mu, s.m, s.k, s.mS, s.w, s.ln, s.cJ, s.aX, s.t, s.a, s.n, s.mk, s.P2, s.K1, s.Kc, s.J, s.R, s.Rd, s.Rr);
  }
  // The ties' weights for the shape above.
  std::vector<Ex> rows(4), lo(1, eO()), gam(5);
  for (int i = 0; i < 4; i++) rows[i] = eB((u64)i + 3);
  for (int c = 0; c < 5; c++) gam[c] = eB((u64)100 + (u64)c);
  std::vector<Ex> wl = tieLeft(T.shp[0], rows, lo), wr = tieRight(T.shp[0], lo, gam);
  printf("TAIL tieLeft=%s\n", vecs(wl).c_str());
  printf("TAIL tieRight=%s\n", vecs(wr).c_str());
}

static void psc_vectors() {
  for (int f = 0; f <= 4; f++) {
    RoundForm form = (RoundForm)f;
    printf("ROUND form=%d values2=%u values3=%u slots=%" PRIu64 "\n", f, roundValues(form), roundValues(form, 3),
           sumcheckSlots(form, 4, 2, 2, 3));
  }
  printf("ROUND layer=%" PRIu64 " tsc=%" PRIu64 " sc3=%" PRIu64 "\n", layerSlots(4), tscSlots(4, 2, 2),
         sc3Slots(4, 2));
  {
    HFork f;
    f.G_ = "t:";
    f.slots(8);
    Psc p;
    p.started = true;
    p.first = 0;
    p.eps = eB(5);
    p.target = eB(11);
    p.claim = eB(13);
    p.vars.push_back(blk::Weight<ExFieldAdapter>::equality(ExFieldAdapter{eB(7)}, 3));
    p.vars.push_back(blk::Weight<ExFieldAdapter>::plain(2));
    p.r.push_back(ExFieldAdapter{eB(2)});
    p.r.push_back(ExFieldAdapter{eB(3)});
    p.start = affC(eB(4));
    Aff kept = affC(eB(9));
    affAdd(kept, affSlot(6), eB(2));
    Aff row = pscRow(f, p, eB(17), kept);
    printf("PSCROW %s\n", affs(row).c_str());
    printf("PSCROW mask=%s\n", vecs(std::vector<Ex>(f.vp.begin(), f.vp.end())).c_str());
  }
  {
    HFork f;
    f.G_ = "t:";
    f.slots(8);
    Psc p;
    p.started = true;
    p.first = 0;
    p.eps = eO();
    p.target = eZ();
    p.claim = eZ();
    p.vars.push_back(blk::Weight<ExFieldAdapter>::equality(ExFieldAdapter{eO()}, 2));
    p.r.push_back(ExFieldAdapter{eO()});
    Aff row = pscRow(f, p, eZ());
    printf("PSCROW one %s\n", affs(row).c_str());
  }
}

int main() {
  power_of_two();
  aff_vectors();
  fork_vectors();
  packing_vectors();
  forest_vectors();
  placez_vectors();
  block_vectors();
  smallness_shape_vectors();
  psc_vectors();
  return 0;
}
