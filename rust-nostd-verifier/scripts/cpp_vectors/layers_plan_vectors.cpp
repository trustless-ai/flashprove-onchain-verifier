// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the layer sub-proofs' plans: the `HPlan2` that `verifier/src/vf_layers_plan.inc`
// builds for every layer group, from the public files alone. The code below is that file's
// per-group block, with the plan-time rounds left unset (the Rust replay compares the shapes,
// counts and arrays; the rounds' round records are compared by the stage's own lane) and the
// attention checks after it omitted. The read lists are `runStage()`'s (`readsZ`/`readsR`).
//
// Usage: layers_plan_vectors <policy.txt> <KL.bin>

#define main cp_verify_original_main
#include "../../verifier/src/cp_verify.cpp"
#undef main

#include <cinttypes>
#include <fstream>
#include <iterator>
#include <string>
#include <vector>

static std::string slurp(const char *path) {
  std::ifstream f(path, std::ios::binary);
  if (!f) {
    std::fprintf(stderr, "layers_plan_vectors: cannot read %s\n", path);
    std::exit(2);
  }
  return std::string(std::istreambuf_iterator<char>(f), std::istreambuf_iterator<char>());
}
static std::vector<u32> read_words(const std::string &b) {
  std::vector<u32> w(b.size() / 4);
  for (size_t i = 0; i < w.size(); i++)
    w[i] = (u32)(u8)b[4 * i] | (u32)(u8)b[4 * i + 1] << 8 | (u32)(u8)b[4 * i + 2] << 16 | (u32)(u8)b[4 * i + 3] << 24;
  return w;
}
static std::string names(const std::vector<std::string> &v) {
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    if (i) s += ",";
    s += v[i];
  }
  if (s.empty()) s = "-";
  return s;
}
static void psh(const ShP &x) {
  std::printf("m=%" PRIu64 " k=%" PRIu64 " mS=%" PRIu64 " w=%d ln=%d cJ=%d aX=%d t=%u a=%u n=%" PRIu64
              " mk=%" PRIu64 " p2=%" PRIu64 " k1=%" PRIu64 " kc=%" PRIu64 " j=%" PRIu64 " r=%" PRIu64
              " rd=%" PRIu64 " rr=%" PRIu64,
              x.m, x.k, x.mS, x.w, x.ln, x.cJ, x.aX, x.t, x.a, x.n, x.mk, x.P2, x.K1, x.Kc, x.J, x.R, x.Rd, x.Rr);
}
static void pplace(const char *kind, u64 g, size_t i, const PlaceF &p) {
  std::printf("LPL g=%" PRIu64 " %s=%zu owner=%d rootIndex=%d haveShape=%d col0=%" PRIu64 " k=%" PRIu64
              " m=%" PRIu64 " haveMatrix=%d hb=%u mS=%" PRIu64 " lanes=%" PRIu64 " padRows=%" PRIu64
              " J=%" PRIu64 " K=%" PRIu64 " off=%" PRIu64 " w=%u sh=",
              g, kind, i, p.owner, p.rootIndex, (int)p.haveShape, p.col0, p.k, p.m, (int)p.haveMatrix, p.hb, p.mS,
              p.lanes, p.padRows, p.J, p.K, p.off, p.w);
  psh(p.sh);
  std::printf("\n");
}

struct P2 {
  HTailF2 tl;
  HFork Fp;
  Tail2 Tp;
  u64 nU[3] = {0, 0, 0};
  u32 ns = 0, used = 0;
  std::function<void(blk::Plan &, unsigned)> rounds;
  size_t NCL = 0, nLin = 0;
  u64 nBatched = 0;
  int lamS = 0;
};

int main(int argc, char **argv) {
  const bool headOnly = argc == 4 && std::string(argv[3]) == "head";
  if (argc != 3 && argc != 4) {
    std::fprintf(stderr, "usage: layers_plan_vectors <policy.txt> <KL.bin> [head]\n");
    return 2;
  }
  const std::string pol = slurp(argv[1]);
  const std::vector<u32> KL = read_words(slurp(argv[2]));
  refuseThrows = true;
  try {
    PolScan PS;
    polPrescan(PS, pol);
    polSkeleton(PS, false);
    polScan(PS, pol);
    Lay y = polLayout(PS);
    setTau(y, y);
    const Hdr &h = PS.h;
    const u64 T = y.T, Lam = y.Lam, NGr = y.NGr, Pd = y.Pd, S2 = y.S2, NN = y.NN, NI = y.NI, dq = y.dq,
              nqk = y.nqk;
    const u64 d = h.d, f = h.f, fe = h.fe;
    const u64 NE = h.NE, LamM = y.LamM;
    const u64 Pf = y.Pf;
    const int lt = (int)h.lt, ll = (int)h.ll, lPf = y.lPf, lfe = y.lfe, lPd = y.lPd, ls = y.ls, la = (int)h.la,
              ldh = y.ldh;
    const u32 lkW = PS.frame.block_log;
    const bool p3 = h.NE > 0;
    const u64 KW_ = 13;
    auto kl = [&](u64 l, int i) { return KL[KW_ * l + i]; };
    (void)kl;
    (void)Pd;
    (void)Pf;
    (void)ldh;
    (void)LamM;
    (void)nqk;
    // The tails: the same construction as context_vectors.cpp.
    std::vector<Tail> tails(NGr);
    const size_t iAD = y.parts[0], iAR = iAD + y.parts[1], iB = iAR + 1, iQA = iB + 1, iXO = iQA + 1, iXI = iXO + 1;
    for (u64 g = 0; g < NGr; g++) {
      Tail &t = tails[g];
      const u64 gid = 1 + g;
      auto req = [&](const std::string &n, u64 m, u64 k) {
        TMat M;
        M.name = n;
        M.m = m;
        M.k = k;
        M.aId = gid * 256 + t.mats.size();
        t.mats.push_back(M);
      };
      for (u64 p = 0; p < y.parts[0]; p++) req("af" + std::to_string(p), y.mrow[0], y.kcol[0]);
      for (u64 p = 0; p < y.parts[1]; p++) req("ad" + std::to_string(p), y.mrow[1], y.kcol[1]);
      req("ar", y.mrow[2], y.kcol[2]);
      req("b", 1ull << h.lmb, y.kbm);
      req("qa", y.mrow[3], y.kcol[3]);
      req("xbO", y.mxb, y.kxb);
      req("xbI", y.mxb, y.kxb);
    }
    for (u64 g = 1; g < NGr; g++) {
      Tail &t = tails[g];
      t.mats[iXI].kind = 1;
      t.mats[iXI].foreign = 0;
      t.mats[iXI].aId = tails[g - 1].mats[iXO].aId;
    }
    // runStage()'s read lists (readsZ, readsR and the block that fills them).
    auto readsZ = [&](const std::string &s) -> std::string {
      if (s == "G" || s == "U" || s == "V" || s == "CN1" || s == "CN2") return "df";
      if (s == "O") return "fiQ";
      if (s == "D") return "fo";
      if (s == "XR") return "d";
      if (s == "LR") return "dr";
      if (s == "LT" || s == "DD" || s == "ROW" || s == "LH" || s == "SEL" || s == "MR" || s == "L3" || s == "CLR")
        return "r";
      if (s == "CQK" || s == "CV") return "fq";
      return "f";
    };
    auto readsR = [&](const std::string &s) -> std::string {
      if (s == "N1") return "rfi";
      if (s == "N2") return "rf";
      if (s == "QK") return "d";
      if (p3) {
        if (s == "G" || s == "U" || s == "XR") return "rd";
        if (s == "D" || s == "DD" || s == "MR") return "r";
      }
      return "";
    };
    std::vector<std::string> tscCalls, rdAF, rdQA, rdXI, rdXO, rdAD, rdAR, rdQS;
    {
      auto has = [](const std::string &s, char c) { return s.find(c) != std::string::npos; };
      std::vector<std::string> zs(y.calls.size()), rs(y.calls.size());
      for (size_t q = 0; q < y.calls.size(); q++)
        for (auto &s : y.calls[q].segs) {
          zs[q] += readsZ(s.name);
          rs[q] += readsR(s.name);
        }
      for (size_t q = 0; q < y.calls.size(); q++)
        if (!rs[q].empty()) tscCalls.push_back(y.calls[q].c.name);
      struct LM {
        char c = 0;
        std::vector<std::string> *v = nullptr;
        bool zv = false, zab = false;
      } lmx[4] = {
          {'f', &rdAF, true, true}, {'q', &rdQA, false, false}, {'i', &rdXI, true, false}, {'o', &rdXO, false, false}};
      auto any = [&](const std::vector<std::string> &v, char c) {
        for (auto &s : v)
          if (has(s, c)) return true;
        return false;
      };
      for (auto &m : lmx) {
        if (any(zs, m.c)) m.v->push_back("Z");
        if (m.zv) m.v->push_back("Z_V");
        if (any(rs, m.c)) m.v->push_back("Y");
        if (m.zab) {
          m.v->push_back("Z_a");
          if (p3) m.v->push_back("Z_b");
        }
      }
      struct SM {
        char c = 0;
        std::vector<std::string> *v = nullptr;
        bool pv = false;
      } smx[3] = {{'d', &rdAD, false}, {'r', &rdAR, true}, {'Q', &rdQS, false}};
      for (auto &m : smx) {
        if (any(zs, m.c)) m.v->push_back("zt");
        if (m.pv) {
          m.v->push_back("P_V");
          m.v->push_back("r_tV");
        }
        if (any(rs, m.c)) m.v->push_back("rt");
      }
    }
    const int lNI = clog2(NI), muV = lNI + lPd + lt, muH = ll + lPf + lt, muH2 = ll - 1 + lfe + lt;
    const u64 GSaf = y.filled[0] * T >> la, GSxb = y.xbFilled * T >> la, GSqa = y.filled[3] * T >> la;
    const size_t wW =
        WPE * (rdAF.size() * GSaf + rdQA.size() * GSqa + (rdXI.size() + rdXO.size()) * GSxb + rdAD.size() * y.filled[1] +
               rdAR.size() * y.filled[2] + rdQS.size() * y.filled[3] + 3 * y.kbm);
    std::printf("STAGE ngr=%" PRIu64 " lam=%" PRIu64 " lamM=%" PRIu64 " ni=%" PRIu64 " nn=%" PRIu64 " ne=%" PRIu64
                " p3=%d muV=%d muH=%d muH2=%d wW=%zu pow=%d stated_hb=%u lidb=%d tau=%u la=%d lt=%d ll=%d lkW=%u\n",
                NGr, Lam, LamM, NI, NN, NE, (int)p3, muV, muH, muH2, wW, POW, statedTarget.hb, LIDB, h.tau, la, lt, ll,
                lkW);
    std::printf("READS tsc=%s af=%s qa=%s xi=%s xo=%s ad=%s ar=%s qs=%s\n", names(tscCalls).c_str(), names(rdAF).c_str(),
                names(rdQA).c_str(), names(rdXI).c_str(), names(rdXO).c_str(), names(rdAD).c_str(), names(rdAR).c_str(),
                names(rdQS).c_str());

    // vf_layers_plan.inc:26-162, with the plan-time rounds left out and the dumps added.
    std::vector<P2> hid(NGr);
    size_t borderCmpF = 0;
    for (u64 g = 0; g < NGr; g++) {
      P2 &P = hid[g];
      P.Fp.G_ = "G" + std::to_string(g) + ":";
      std::vector<TMat> mats = tails[g].mats;
      std::vector<int> txOf(mats.size(), -1);
      std::vector<T2Foreign> ft;
      std::vector<u32> aTX;
      for (size_t mu = 0; mu < mats.size(); mu++) {
        TMat &M = mats[mu];
        if (M.kind == 0 && (mu == iXO || mu == iQA)) {
          txOf[mu] = (int)aTX.size();
          aTX.push_back(2);
        } else if (M.kind == 1) {
          T2Foreign fm;
          fm.name = "PXf" + std::to_string(ft.size());
          fm.K = M.k;
          fm.a = 2;
          fm.m = M.m;
          fm.wp = M.wp;
          M.foreign = (int)ft.size();
          M.ttOff = 0;
          ft.push_back(fm);
        } else if (M.kind == 2)
          refuse("internal-weight-matrix");
      }
      const bool hasU[4] = {false, false, true, false};
      P.tl.shape(mats, txOf, ft, hasU, h.tau);
      const HForest &fo = y.fo;
      size_t msg = forestElems(fo);
      const size_t nT = tscCalls.empty() ? 0 : 1;
      {
        const int wi = clog2(Lam);
        u64 tot =
            4 * (1ull << (wi + clog2(d))) + (1ull << (wi + clog2(dq))) + (1ull << (wi + clog2(f))) + 2 * (1ull << wi);
        if (p3) {
          const int wm = clog2(LamM), le = clog2(NE);
          tot += (1ull << (wm + clog2(d))) + (1ull << wm) + 2 * (1ull << (wm + le)) +
                 LamM * (2 * (1ull << (le + clog2(d))) + (1ull << (le + clog2(fe))));
        }
        P.lamS = clog2(tot);
      }
      P.NCL = 6 * Lam + (p3 ? 4 * LamM : 0) + (g == 0 ? 1 : 0);
      {
        const size_t lin = forestLins(fo) + 3 + (2 + ((u64)ledNO() + (u64)ledNS() + (u64)ledLines()) * NI) +
                           (nT ? NN * Lam + (p3 ? LamM * (1 + NE) : 0) : 0) + 3 + (p3 ? 3 : 0) + (p3 ? LamM : 0) + 3 +
                           (g == 0 ? 1 : 0) + 3 + 1;
        const size_t nX4 =
            rdAF.size() * (size_t)y.parts[0] * (size_t)(y.mrow[0] >> la) + rdQA.size() * (size_t)(y.mrow[3] >> la) +
            (rdXI.size() + (g == 0 ? 1 : 0) + rdXO.size()) * (size_t)(y.mxb >> la) +
            rdAD.size() * (size_t)y.parts[1] * (size_t)(y.mrow[1] >> lt) + rdAR.size() * (size_t)(y.mrow[2] >> lt) +
            rdQS.size() * (size_t)(y.mrow[3] >> lt) + 3;
        P.nLin = lin + P.tl.lins(nX4);
        P.nBatched = P.nLin + P.tl.equationsF(nX4);
      }
      msg += (size_t)ledNS() * NI + (size_t)layerSlots(muV) + (size_t)ledNP() * NI;
      msg += (size_t)tscSlots(lt, (u64)ledNO() * NI, 2);
      if (nT) msg += (size_t)tscSlots(lt, NN * Lam + (p3 ? LamM * (1 + NE) : 0), 1);
      msg += (size_t)sumcheckSlots(RoundForm::SUM2, P.lamS, 2 + 1 + (p3 ? LamM : 0) + P.NCL - (g == 0 ? 1 : 0), 2);
      msg += (size_t)layerSlots(muH) + (p3 ? (size_t)layerSlots(muH2) : 0) + (g == 0 ? 1 : 0) +
             wsForkSlots((int)lkW) + P.tl.smallElems();
      P.nU[2] = wW / WPE + (g == 0 ? mats[iXI].k * (mats[iXI].m >> la) : 0);
      P.tl.addTrees(P.Fp, P.Tp, P.nU, aTX, statedTarget.hb - (u32)POW);
      t2Plan(P.Fp, P.Tp);
      if (P.tl.ix.FT.size() != (g ? 1u : 0u)) refuse("internal-g-owner-shape");
      if (g) {
        const P2 &O = hid[g - 1];
        if (O.tl.ix.TX.empty() || P.tl.ix.FT.empty() ||
            !t2SameShape(O.Tp.nt[O.tl.ix.TX.back()], O.Fp.trees[O.tl.ix.TX.back()], P.Tp.nt[P.tl.ix.FT[0]],
                         P.Fp.trees[P.tl.ix.FT[0]]))
          refuse("internal-g-owner-shape");
      }
      P.tl.ownerIs((int)g);
      if (g) {
        P.tl.borderMeans(0, (int)g - 1, (int)(hid[g - 1].tl.pkMat.size() + hid[g - 1].tl.ix.TX.size()) - 1);
        const char *df = samePlaceF(hid[g - 1].tl.ownEntry("stream"), P.tl.plFor[0]);
        if (*df) refuse(std::string("internal-g-owner-place-") + df);
        borderCmpF++;
      }
      if (msg >= (1ull << 30)) refuse("hid-g-slots");
      P.used = (u32)msg;
      P.ns = (u32)msg;
      trimL(P.Fp);
    }
    const size_t borderCmpLayers = borderCmpF;
    // ---- The output head's layout (HLy), as in context_vectors.cpp. ----
    struct HL {
      u64 JV = 0, JVa = 0, oE = 0, feat = 0, filled = 0, k = 0, m = 0, oAw = 0, oRa = 0, oD1 = 0, oD2 = 0,
          fillD = 0, kD = 0, mD = 0, fillR = 0, kR = 0, mR = 0, kb = 0;
      std::vector<CallD> calls;
      std::vector<u64> tauFE;
      HForest fs;
    } HLy;
    {
      const u64 Vv = h.V, S2 = y.S2;
      HLy.JV = (Vv + S2 - 1) / S2 * S2;
      HLy.oAw = 0;
      HLy.oRa = 2 * d;
      HLy.oD1 = 4 * d;
      HLy.oD2 = 4 * d + 2 * HLy.JV;
      HLy.oE = 4 * d + 3 * HLy.JV;
      HLy.feat = 4 * d + (3 + EXC) * HLy.JV;
      HLy.JVa = 1ull << (clog2(HLy.JV) - 1);
      HLy.m = 1ull << h.lmhf;
      {
        u64 unit = h.NHf * (HLy.m / T);
        HLy.filled = (HLy.feat + unit - 1) / unit * unit;
        HLy.k = HLy.filled / unit;
      }
      HLy.mD = 1ull << h.lmhd;
      {
        u64 unit = HLy.mD / T;
        HLy.fillD = (2 * d + unit - 1) / unit * unit;
        HLy.kD = HLy.fillD / unit;
      }
      HLy.mR = 1ull << h.lmhr;
      {
        u64 unit = HLy.mR / T;
        HLy.fillR = ((u64)ledNRH() + unit - 1) / unit * unit;
        HLy.kR = HLy.fillR / unit;
      }
      struct SD {
        std::string name, kind;
        u64 n = 0;
      };
      std::vector<SD> sd = {{"NF", "R16", d},      {"NFH", "R16", d},     {"HD0", "R16", HLy.JV},
                            {"HD1", "R16", HLy.JV},  {"ROW", "R8", (u64)ledNRH()}, {"HD2", "R8", HLy.JV},
                            {"CNF", "FC", d},      {"HE0", "FE", HLy.JVa},  {"HE1", "FE", HLy.JV - HLy.JVa}};
      CallLines cl = PS.polCallsH;
      if (cl.empty())
        cl = {{"R16a", "R16", "NF", "NFH", "HD0"},
              {"R16b", "R16", "HD1"},
              {"R8", "R8", "ROW", "HD2"},
              {"FEa", "FE", "HE0"},
              {"FEb", "FE", "HE1"},
              {"FC", "FC", "CNF"}};
      {
        static const u64 NQ[7] = {4034748383ull, 4162825045ull, 4228380000ull, 4261543596ull,
                                  4278222806ull, 4286586875ull, 4290775040ull};
        const u64 N = h.tabS < h.digSh ? 484 : NQ[h.tabS - h.digSh - 4];
        HLy.tauFE.resize(65536);
        u128 G = (u128)1 << (h.famF + 17);
        for (u64 u = 0; u < 65536; u++) {
          HLy.tauFE[u] = u + ((u64)((G + 131071) >> 17) << 16);
          G = (G * N + 0xFFFFFFFFull) >> 32;
        }
      }
      std::vector<char> seen(sd.size(), 0);
      for (auto &ln : cl) {
        CallD cd;
        cd.c.name = ln[0];
        cd.kind = ln[1];
        for (size_t i = 2; i < ln.size(); i++) {
          size_t j = 0;
          while (j < sd.size() && sd[j].name != ln[i]) j++;
          if (j == sd.size() || seen[j] || sd[j].kind != ln[1]) refuse("policy-call-list-H");
          seen[j] = 1;
          Seg s;
          s.name = sd[j].name;
          s.n = sd[j].n;
          cd.segs.push_back(s);
        }
        HLy.calls.push_back(cd);
      }
      const int nminH = NMINH ? NMINH : (int)h.nmin;
      for (size_t q = 0; q < HLy.calls.size(); q++) {
        CallD &cd = HLy.calls[q];
        int fl = nminH - (int)h.lt;
        place(cd, fl < 0 ? 0 : fl);
        Call &c = cd.c;
        c.n = cd.lJ + (int)h.lt;
        c.kappa = 5;
        c.k = cd.kind == "R8" ? 8 : 16;
        if (cd.kind == "FC") {
          c.fn = 1;
          c.t0 = 32768;
          c.tau = &y.tauFC;
        }
        if (cd.kind == "FE") {
          c.fn = 1;
          c.t0 = 0;
          c.tau = &HLy.tauFE;
        }
      }
      std::vector<Call *> clH;
      for (auto &cd : HLy.calls) clH.push_back(&cd.c);
      HLy.fs = forestShape(clH, LIDB);
      HLy.kb = forestPlaneCols(HLy.fs, (int)h.lmbH);
      for (size_t q = 0; q < HLy.calls.size(); q++) HLy.calls[q].c.iota = HLy.fs.iota[q];
      HLy.fs.pub.assign((size_t)HLy.fs.NT, 0);
      const int cs = HLy.fs.dT - (int)h.lt;
      for (size_t q = 0; q < HLy.calls.size(); q++) {
        const CallD &cd = HLy.calls[q];
        u64 *pb = HLy.fs.pub.data() + HLy.fs.first[q];
        for (u64 j = 0; j < cd.J; j++)
          if (!cd.used[j]) pb[j >> cs] += T;
        for (auto &s : cd.segs)
          if (s.name[0] == 'H') {
            const u64 v0 = s.name == "HE1" ? HLy.JVa : 0;
            for (u64 x = Vv > v0 ? Vv - v0 : 0; x < s.n; x++) pb[s.pos[x] >> cs] += T;
          }
      }
    }
    // ---- The output head's plan (PH2), vf_output_head_plan.inc:26-145. ----
    struct HP {
      HTailF2 tl;
      HFork Fp;
      Tail2 Tp;
      u64 nU[3] = {0, 0, 0};
      u32 ns = 0;
      size_t nMsg = 0, nLin = 0, NCL = 1;
      blk::HeadRounds own;
      int lamS = 0;
    } PH2;
    {
      HP &P = PH2;
      const u32 hb = statedTarget.hb - (u32)POW;
      const HL &L = HLy;
      const HForest &fs = L.fs;
      P.Fp.G_ = "H:";
      if ((u32)clog2(h.V) > lkW) refuse("hid-vocab-cols");
      if (fs.cl.size() != L.calls.size() || fs.pub.size() != (size_t)fs.NT || L.kb != forestPlaneCols(fs, (int)h.lmbH))
        refuse("internal-h-forest");
      std::vector<TMat> mats;
      const u64 gidH = 1 + NGr;
      auto req = [&](const std::string &n, u64 m, u64 k, u32 wp) {
        TMat M;
        M.name = n;
        M.m = m;
        M.k = k;
        M.wp = wp;
        M.aId = gidH * 256 + mats.size();
        mats.push_back(M);
      };
      for (u64 q = 0; q < h.NHf; q++) req("hf" + std::to_string(q), L.m, L.k, 0);
      req("hd", L.mD, L.kD, 0);
      req("hr", L.mR, L.kR, 0);
      req("bH", 1ull << h.lmbH, L.kb, 0);
      req("xbL", y.mxb, y.kxb, 0);
      {
        TMat &M = mats.back();
        M.kind = 1;
        M.foreign = 0;
        M.ttOff = 0;
        M.aId = hid[NGr - 1].tl.mats[iXO].aId;
      }
      T2Foreign fx;
      fx.name = "PXf0";
      fx.K = y.kxb;
      fx.a = 2;
      fx.m = y.mxb;
      fx.wp = 0;
      const bool hasU[4] = {false, false, true, false};
      P.tl.shape(mats, std::vector<int>(mats.size(), -1), {fx}, hasU, h.tau);
      size_t msg = forestElems(fs);
      P.lamS = lPd;
      const int muVh = lPd + lt;
      if (muVh < 9) refuse("shape-product-layer-H");
      P.NCL = 1;
      msg += P.tl.smallElems() + (size_t)ledNS() + (size_t)layerSlots(muVh) + (size_t)ledNP() +
             (size_t)tscSlots(lt, (u64)ledNO(), 2) + (size_t)tscSlots(lt, 2, 2) +
             (size_t)tscSlots(lt, 2, 2, P.lamS) + wsForkSlots((int)lkW);
      const u64 GSx = y.kxb * (y.mxb >> la);
      const u64 nhfZ = 2;
      P.nU[2] = nhfZ * (L.filled * T >> la) + 2 * GSx + 2 * L.fillD + 6 * L.fillR + 3 * L.kb;
      const size_t readsH = nhfZ * h.NHf * (L.m >> la) + 2 * (L.mD >> lt) + 6 * (L.mR >> lt) + 3 + 2 * (y.mxb >> la);
      P.nLin = forestLins(fs) + 3 + (size_t)(1 + 1 + ledNO() + ledNS() + ledLines()) + 3 + 1 + 4 + 3 + 2 + 1 +
               P.tl.lins(readsH);
      P.tl.addTrees(P.Fp, P.Tp, P.nU, {}, hb);
      if (P.Tp.nt.size() != (1 + P.tl.pkMat.size() + 2 + 1)) refuse("internal-h-tree-list");
      t2Plan(P.Fp, P.Tp);
      {
        const P2 &O = hid[NGr - 1];
        if (O.tl.ix.TX.empty()) refuse("internal-h-owner-TX");
        if (!t2SameShape(O.Tp.nt[O.tl.ix.TX.back()], O.Fp.trees[O.tl.ix.TX.back()], P.Tp.nt[P.tl.ix.FT[0]],
                         P.Fp.trees[P.tl.ix.FT[0]]))
          refuse("internal-h-owner-shape");
        {
          P.tl.borderMeans(0, (int)NGr - 1, (int)(O.tl.pkMat.size() + O.tl.ix.TX.size()) - 1);
          const char *df = samePlaceF(O.tl.ownEntry("stream"), P.tl.plFor[0]);
          if (*df) refuse(std::string("internal-h-owner-place-") + df);
          borderCmpF++;
        }
      }
      if (msg >= (1ull << 30)) refuse("hid-h-slots");
      P.nMsg = msg;
      P.own.lt = (unsigned)lt, P.own.lPd = (unsigned)lPd, P.own.lkW = (unsigned)lkW;
      P.own.sums = (unsigned)ledNS(), P.own.products = (unsigned)ledNP(), P.own.row_values = (unsigned)ledNO();
      P.own.rows = P.nLin + P.tl.equationsF(readsH);
      P.ns = (u32)msg;
      trimL(P.Fp);
    }
    if (headOnly) {
      std::printf("HEAD nU=%" PRIu64 ",%" PRIu64 ",%" PRIu64 " nMsg=%zu ns=%u NCL=%zu nLin=%zu lamS=%d\n", PH2.nU[0],
                  PH2.nU[1], PH2.nU[2], PH2.nMsg, PH2.ns, PH2.NCL, PH2.nLin, PH2.lamS);
      std::printf("HOWN lt=%u lPd=%u lkW=%u sums=%u products=%u row_values=%u rows=%" PRIu64 "\n", PH2.own.lt,
                  PH2.own.lPd, PH2.own.lkW, PH2.own.sums, PH2.own.products, PH2.own.row_values, PH2.own.rows);
      for (size_t i = 0; i < PH2.tl.mats.size(); i++) {
        const TMat &M = PH2.tl.mats[i];
        std::printf("HMAT i=%zu name=%s m=%" PRIu64 " k=%" PRIu64 " kind=%d foreign=%d ttOff=%" PRIu64
                    " aId=%" PRIu64 " wp=%u\n",
                    i, M.name.c_str(), M.m, M.k, M.kind, M.foreign, M.ttOff, M.aId, M.wp);
      }
      for (size_t ti = 0; ti < PH2.Fp.trees.size(); ti++) {
        const HTree &X = PH2.Fp.trees[ti];
        std::printf("HT ti=%zu name=%s kind=%c R=%" PRIu64 " K=%" PRIu64 " owner=%d rows=%zu\n", ti, X.name.c_str(),
                    X.kind, X.R, X.K, (int)X.owner, X.rows.size());
      }
      for (size_t ti = 0; ti < PH2.Tp.nt.size(); ti++) {
        const N2 &n = PH2.Tp.nt[ti];
        std::printf("HNT ti=%zu ec=%u a=%u foreign=%d outside=%d P=%d ", ti, n.ec, n.a, (int)n.foreign,
                    (int)n.outside, (int)n.P);
        psh(n.p);
        std::printf("\n");
      }
      std::printf("HIX u=%d,%d,%d,%d tt=%d bt=%d zz=%d yy=%d kk=%d bz=%d tx=", PH2.tl.ix.U[0], PH2.tl.ix.U[1],
                  PH2.tl.ix.U[2], PH2.tl.ix.U[3], PH2.tl.ix.TT, PH2.tl.ix.BT, PH2.tl.ix.ZZ, PH2.tl.ix.YY,
                  PH2.tl.ix.KK, PH2.tl.ix.BZ);
      for (size_t i = 0; i < PH2.tl.ix.TX.size(); i++) std::printf("%s%d", i ? "," : "", PH2.tl.ix.TX[i]);
      std::printf(" ft=");
      for (size_t i = 0; i < PH2.tl.ix.FT.size(); i++) std::printf("%s%d", i ? "," : "", PH2.tl.ix.FT[i]);
      std::printf(" pk=");
      for (size_t i = 0; i < PH2.tl.ix.PK.size(); i++) std::printf("%s%d", i ? "," : "", PH2.tl.ix.PK[i]);
      std::printf(" count=%d\n", PH2.tl.ix.count);
      for (size_t i = 0; i < PH2.tl.plOwn.size(); i++) pplace("own", 0, i, PH2.tl.plOwn[i]);
      for (size_t i = 0; i < PH2.tl.plFor.size(); i++) pplace("for", 0, i, PH2.tl.plFor[i]);
    }
    if (headOnly) return 0;
    std::printf("BORDER cmp=%zu\n", borderCmpLayers);
    for (u64 g = 0; g < NGr; g++) {
      const P2 &P = hid[g];
      std::printf("LAYER g=%" PRIu64 " nU=%" PRIu64 ",%" PRIu64 ",%" PRIu64 " ns=%u used=%u lamS=%d NCL=%zu nLin=%zu nBatched=%" PRIu64 "\n",
                  g, P.nU[0], P.nU[1], P.nU[2], P.ns, P.used, P.lamS, P.NCL, P.nLin, P.nBatched);
      for (size_t i = 0; i < P.tl.mats.size(); i++) {
        const TMat &M = P.tl.mats[i];
        std::printf("LMAT g=%" PRIu64 " mu=%zu name=%s m=%" PRIu64 " k=%" PRIu64 " kind=%d foreign=%d ttOff=%" PRIu64
                    " aId=%" PRIu64 " wp=%u\n",
                    g, i, M.name.c_str(), M.m, M.k, M.kind, M.foreign, M.ttOff, M.aId, M.wp);
      }
      for (size_t ti = 0; ti < P.Fp.trees.size(); ti++) {
        const HTree &X = P.Fp.trees[ti];
        std::printf("LT g=%" PRIu64 " ti=%zu name=%s kind=%c R=%" PRIu64 " K=%" PRIu64 " owner=%d rows=%zu\n", g, ti,
                    X.name.c_str(), X.kind, X.R, X.K, (int)X.owner, X.rows.size());
      }
      for (size_t ti = 0; ti < P.Tp.nt.size(); ti++) {
        const N2 &n = P.Tp.nt[ti];
        std::printf("LNT g=%" PRIu64 " ti=%zu ec=%u a=%u foreign=%d outside=%d P=%d ", g, ti, n.ec, n.a, (int)n.foreign,
                    (int)n.outside, (int)n.P);
        psh(n.p);
        std::printf("\n");
      }
      std::printf("LIX g=%" PRIu64 " u=%d,%d,%d,%d tt=%d bt=%d zz=%d yy=%d kk=%d bz=%d tx=", g, P.tl.ix.U[0], P.tl.ix.U[1],
                  P.tl.ix.U[2], P.tl.ix.U[3], P.tl.ix.TT, P.tl.ix.BT, P.tl.ix.ZZ, P.tl.ix.YY, P.tl.ix.KK, P.tl.ix.BZ);
      for (size_t i = 0; i < P.tl.ix.TX.size(); i++) std::printf("%s%d", i ? "," : "", P.tl.ix.TX[i]);
      std::printf(" ft=");
      for (size_t i = 0; i < P.tl.ix.FT.size(); i++) std::printf("%s%d", i ? "," : "", P.tl.ix.FT[i]);
      std::printf(" pk=");
      for (size_t i = 0; i < P.tl.ix.PK.size(); i++) std::printf("%s%d", i ? "," : "", P.tl.ix.PK[i]);
      std::printf(" count=%d\n", P.tl.ix.count);
      for (size_t i = 0; i < P.tl.plOwn.size(); i++) pplace("own", g, i, P.tl.plOwn[i]);
      for (size_t i = 0; i < P.tl.plFor.size(); i++) pplace("for", g, i, P.tl.plFor[i]);
    }
  } catch (Refusal &r) {
    std::printf("REFUSED %s\n", r.name.c_str());
    return 1;
  }
  return 0;
}
