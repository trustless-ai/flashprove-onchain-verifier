// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the stage context around the layer and output-head sub-proofs: the KL.bin words, the
// layer range-check matrices (`tails`), W's layout (`wsLay`) and the output head's layout (`HLy`:
// its matrices, lookup calls and forest). The code below is the corresponding part of
// `runStage()` in `verifier/src/cp_verify.cpp`, with the proof/hash side omitted.
//
// Usage: context_vectors <policy.txt> <KL.bin>

#define main cp_verify_original_main
#include "../../verifier/src/cp_verify.cpp"
#undef main

#include <cinttypes>
#include <fstream>
#include <iterator>
#include <tuple>

static std::string slurp(const char *path) {
  std::ifstream f(path, std::ios::binary);
  if (!f) {
    std::fprintf(stderr, "context_vectors: cannot read %s\n", path);
    std::exit(2);
  }
  return std::string(std::istreambuf_iterator<char>(f), std::istreambuf_iterator<char>());
}
static std::vector<u32> read_words(const std::string &b) {
  if (b.size() % 4) {
    std::fprintf(stderr, "context_vectors: KL is not a whole number of words\n");
    std::exit(2);
  }
  std::vector<u32> w(b.size() / 4);
  for (size_t i = 0; i < w.size(); i++)
    w[i] = (u32)(u8)b[4 * i] | (u32)(u8)b[4 * i + 1] << 8 | (u32)(u8)b[4 * i + 2] << 16 | (u32)(u8)b[4 * i + 3] << 24;
  return w;
}
static u64 hash_words(const std::vector<u32> &v) {
  u64 h = 0;
  for (u32 x : v) h = mix64(h + x);
  return h;
}
static u64 hash_words64(const std::vector<u64> &v) {
  u64 h = 0;
  for (u64 x : v) h = mix64(h + x);
  return h;
}
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
static std::string segs(const CallD &c) {
  std::string s;
  for (size_t i = 0; i < c.segs.size(); i++) {
    if (i) s += ";";
    s += c.segs[i].name + ":" + std::to_string(c.segs[i].n);
  }
  return s;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    std::fprintf(stderr, "usage: context_vectors <policy.txt> <KL.bin>\n");
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
    PS.h = parseHeader(PS.st);
    const Hdr &h = PS.h;
    Lay y = layout(h, PS.polCalls);
    const u64 T = y.T, d = h.d, dh = h.dh, dq = y.dq, f = h.f, fe = h.fe, NE = h.NE;
    const bool p3 = h.NE > 0;
    const u64 NGr = y.NGr;
    const u32 lkW = PS.frame.block_log;
    const u64 KW_ = 13;
    printf("KL len=%zu hash=%016" PRIx64 " head=%s\n", KL.size(), hash_words(KL),
           u64s(std::vector<u64>(KL.begin(), KL.begin() + std::min<size_t>(8, KL.size()))).c_str());

    // W's layout.
    WsLay wsLay;
    {
      WsShape s;
      s.D = h.D;
      s.L = h.L;
      s.d = d;
      s.dh = dh;
      s.dkv = y.dkv;
      s.dq = dq;
      s.f = f;
      s.fe = fe;
      s.NE = NE;
      s.V = h.V;
      s.eh = 1;
      wsSetMoe(s, p3 ? 1 : 0);
      wsLay.build(s, lkW);
    }
    printf("WS lk=%d m0=%" PRIu64 " units=%zu\n", wsLay.lk, wsLay.m0, wsLay.U.size());
    for (size_t i = 0; i < wsLay.U.size(); i++) {
      const WsUnit &u = wsLay.U[i];
      printf("WSUNIT i=%zu X=%u l=%u nlw=%d ncb=%d rows=%" PRIu64 " off=%" PRIu64 "\n", i, u.X, u.l, u.nlw,
             u.ncb, u.rows, u.off);
    }

    // tails[g].
    std::vector<Tail> tails(NGr);
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
    const size_t iAD = y.parts[0], iAR = iAD + y.parts[1], iB = iAR + 1, iQA = iB + 1, iXO = iQA + 1, iXI = iXO + 1;
    for (u64 g = 1; g < NGr; g++) {
      Tail &t = tails[g];
      t.mats[iXI].kind = 1;
      t.mats[iXI].foreign = 0;
      t.mats[iXI].aId = tails[g - 1].mats[iXO].aId;
    }
    for (u64 g = 0; g < NGr; g++)
      for (size_t i = 0; i < tails[g].mats.size(); i++) {
        const TMat &m = tails[g].mats[i];
        printf("TAIL g=%" PRIu64 " i=%zu name=%s m=%" PRIu64 " k=%" PRIu64 " kind=%d foreign=%d ttOff=%" PRIu64
               " aId=%" PRIu64 "\n",
               g, i, m.name.c_str(), m.m, m.k, m.kind, m.foreign, m.ttOff, m.aId);
      }
    printf("IDX iAF=%zu iAD=%zu iAR=%zu iB=%zu iQA=%zu iXO=%zu iXI=%zu\n", (size_t)0, (size_t)iAD, iAR, iB, iQA, iXO, iXI);

    // The output head's layout.
    struct HL {
      u64 JV = 0, JVa = 0, oE = 0, feat = 0, filled = 0, k = 0, m = 0, oAw = 0, oRa = 0, oD1 = 0, oD2 = 0,
          fillD = 0, kD = 0, mD = 0, fillR = 0, kR = 0, mR = 0, kb = 0;
      std::vector<CallD> calls;
      std::vector<u64> tauFE;
      HForest fs;
    } L;
    {
      const u64 Vv = h.V, S2 = y.S2;
      L.JV = (Vv + S2 - 1) / S2 * S2;
      L.oAw = 0;
      L.oRa = 2 * d;
      L.oD1 = 4 * d;
      L.oD2 = 4 * d + 2 * L.JV;
      L.oE = 4 * d + 3 * L.JV;
      L.feat = 4 * d + (3 + EXC) * L.JV;
      L.JVa = 1ull << (clog2(L.JV) - 1);
      L.m = 1ull << h.lmhf;
      {
        u64 unit = h.NHf * (L.m / T);
        L.filled = (L.feat + unit - 1) / unit * unit;
        L.k = L.filled / unit;
      }
      L.mD = 1ull << h.lmhd;
      {
        u64 unit = L.mD / T;
        L.fillD = (2 * d + unit - 1) / unit * unit;
        L.kD = L.fillD / unit;
      }
      L.mR = 1ull << h.lmhr;
      {
        u64 unit = L.mR / T;
        L.fillR = ((u64)ledNRH() + unit - 1) / unit * unit;
        L.kR = L.fillR / unit;
      }
      struct SD {
        std::string name, kind;
        u64 n = 0;
      };
      std::vector<SD> sd = {{"NF", "R16", d},      {"NFH", "R16", d},     {"HD0", "R16", L.JV},
                            {"HD1", "R16", L.JV},  {"ROW", "R8", (u64)ledNRH()}, {"HD2", "R8", L.JV},
                            {"CNF", "FC", d},      {"HE0", "FE", L.JVa},  {"HE1", "FE", L.JV - L.JVa}};
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
        L.tauFE.resize(65536);
        u128 G = (u128)1 << (h.famF + 17);
        for (u64 u = 0; u < 65536; u++) {
          L.tauFE[u] = u + ((u64)((G + 131071) >> 17) << 16);
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
        L.calls.push_back(cd);
      }
      const int nminH = NMINH ? NMINH : (int)h.nmin;
      for (size_t q = 0; q < L.calls.size(); q++) {
        CallD &cd = L.calls[q];
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
          c.tau = &L.tauFE;
        }
      }
      std::vector<Call *> clH;
      for (auto &cd : L.calls) clH.push_back(&cd.c);
      L.fs = forestShape(clH, LIDB);
      L.kb = forestPlaneCols(L.fs, (int)h.lmbH);
      for (size_t q = 0; q < L.calls.size(); q++) L.calls[q].c.iota = L.fs.iota[q];
      L.fs.pub.assign((size_t)L.fs.NT, 0);
      const int cs = L.fs.dT - (int)h.lt;
      for (size_t q = 0; q < L.calls.size(); q++) {
        const CallD &cd = L.calls[q];
        u64 *pb = L.fs.pub.data() + L.fs.first[q];
        for (u64 j = 0; j < cd.J; j++)
          if (!cd.used[j]) pb[j >> cs] += T;
        for (auto &s : cd.segs)
          if (s.name[0] == 'H') {
            const u64 v0 = s.name == "HE1" ? L.JVa : 0;
            for (u64 x = Vv > v0 ? Vv - v0 : 0; x < s.n; x++) pb[s.pos[x] >> cs] += T;
          }
      }
    }
    printf("HL JV=%" PRIu64 " JVa=%" PRIu64 " oE=%" PRIu64 " feat=%" PRIu64 " filled=%" PRIu64 " k=%" PRIu64
           " m=%" PRIu64 " oAw=%" PRIu64 " oRa=%" PRIu64 " oD1=%" PRIu64 " oD2=%" PRIu64 " fillD=%" PRIu64
           " kD=%" PRIu64 " mD=%" PRIu64 " fillR=%" PRIu64 " kR=%" PRIu64 " mR=%" PRIu64 " kb=%" PRIu64 "\n",
           L.JV, L.JVa, L.oE, L.feat, L.filled, L.k, L.m, L.oAw, L.oRa, L.oD1, L.oD2, L.fillD, L.kD, L.mD,
           L.fillR, L.kR, L.mR, L.kb);
    printf("HL tauFE len=%zu hash=%016" PRIx64 " first=%" PRIu64 " last=%" PRIu64 "\n", L.tauFE.size(),
           hash_words64(L.tauFE), L.tauFE[0], L.tauFE.back());
    for (size_t q = 0; q < L.calls.size(); q++) {
      const CallD &c = L.calls[q];
      printf("HLCALL q=%zu name=%s kind=%s n=%d iota=%d kappa=%d k=%d fn=%d t0=%" PRIu64 " lJ=%d J=%" PRIu64
             " segs=%s\n",
             q, c.c.name.c_str(), c.kind.c_str(), c.c.n, c.c.iota, c.c.kappa, c.c.k, c.c.fn, c.c.t0, c.lJ, c.J,
             segs(c).c_str());
    }
    const HForest &H = L.fs;
    printf("HLFOREST dT=%d kT=%d NT=%d rK=%d NC=%d cK=%d iota=%s first=%s pub=%s padding=%" PRIu64 "\n", H.dT,
           H.kT, H.NT, H.rK, H.NC, H.cK, i32s(H.iota).c_str(), i32s(H.first).c_str(), u64s(H.pub).c_str(),
           H.padding());
    // A few RoPE entries.
    auto klRp = [&](u64 l) {
      return KL[KW_ * l + KW_ - 1];
    };
    auto ropeC = [&](u64 l, u64 t, u64 i, bool sine) -> i64 {
      if (l != ~0ull && !klRp(l)) return sine ? 0 : (i64)1 << h.cs;
      double ang = (double)t * pow((double)h.theta0, -2.0 * (double)i / (double)dh);
      return (i64)round((double)(1u << h.cs) * (sine ? sin(ang) : cos(ang)));
    };
    for (u64 l = 0; l < h.L; l++)
      for (auto [t, i, sine] : {std::tuple<u64, u64, bool>{0, 0, false}, {1, 0, false}, {3, 1, true},
                                 {T - 1, dh / 2 - 1, false}}) {
        printf("ROPE l=%" PRIu64 " t=%" PRIu64 " i=%" PRIu64 " sine=%d v=%" PRId64 "\n", l, t, i, (int)sine,
               ropeC(l, t, i, sine));
      }
  } catch (Refusal &r) {
    printf("REFUSED %s\n", r.name.c_str());
    return 1;
  }
  return 0;
}
