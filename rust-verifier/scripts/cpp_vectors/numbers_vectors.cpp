// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Deterministic vectors for blocks/numbers/{real,setting,codes}.h, for the Rust port. The tool
// includes the C++ headers and changes no source of theirs.
//
// Build (from the repository root):
//   clang++ -O2 -std=c++17 -Iblocks -DBLK_FIELD=2 -o /tmp/numbers_vectors \
//     rust-verifier/scripts/cpp_vectors/numbers_vectors.cpp

#include "numbers/codes.h"
#include "numbers/real.h"
#include "numbers/setting.h"

#include <cstdio>
#include <string>

using namespace blk;

namespace {
u64 state = 0x243F6A8885A308D3ull;
u64 rnd() {
  u64 z = (state += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}

Big rbig() {
  Big x(rnd());
  if (rnd() % 3 == 0) x = x * Big(rnd() | 1);
  if (rnd() % 3 == 0) x = x.shl(rnd() % 200);
  return x;
}
Real rreal() { return Real(rbig(), (long)(rnd() % 200) - 100); }
Real rpos() { return Real(rbig(), (long)(rnd() % 80) - 40); }

std::string bh(const Big &x) {
  if (x.zero()) return "0";
  std::string s;
  char t[9];
  for (size_t i = 0; i < x.w.size(); i++) {
    std::snprintf(t, sizeof t, "%08x", x.w[i]);
    if (i) s += ",";
    s += t;
  }
  return s;
}
std::string rh(const Real &x) { return bh(x.m) + "@" + std::to_string(x.e); }
std::string dh(const Bound &x) {
  return rh(x.lo) + "|" + rh(x.hi) + "|" + (x.bad ? "1" : "0");
}
std::string bound_line(const char *tag, const Bound &x) { return std::string(tag) + "\t" + dh(x); }
} // namespace

int main() {
  // Big.
  for (int i = 0; i < 120; i++) {
    Big a = rbig(), b = rbig();
    if (b.zero()) b = Big(1);
    std::printf("B\tadd\t%s\t%s\t%s\n", bh(a).c_str(), bh(b).c_str(), bh(a + b).c_str());
    std::printf("B\tmul\t%s\t%s\t%s\n", bh(a).c_str(), bh(b).c_str(), bh(a * b).c_str());
    if (Big::cmp(a, b) >= 0)
      std::printf("B\tsub\t%s\t%s\t%s\n", bh(a).c_str(), bh(b).c_str(), bh(a - b).c_str());
    else
      std::printf("B\tsub\t%s\t%s\t%s\n", bh(b).c_str(), bh(a).c_str(), bh(b - a).c_str());
    Big q, r;
    Big::divmod(a, b, q, r);
    std::printf("B\tdiv\t%s\t%s\t%s\t%s\n", bh(a).c_str(), bh(b).c_str(), bh(q).c_str(), bh(r).c_str());
    std::printf("B\tsqrt\t%s\t%s\n", bh(a).c_str(), bh(Big::isqrt(a)).c_str());
    const u64 pe = rnd() % 9;
    std::printf("B\tpow\t%s\t%llu\t%s\n", bh(a).c_str(), (unsigned long long)pe,
                bh(Big::pow(a, pe)).c_str());
    const size_t sh = rnd() % 260;
    std::printf("B\tshl\t%s\t%zu\t%s\n", bh(a).c_str(), sh, bh(a.shl(sh)).c_str());
    std::printf("B\tshr\t%s\t%zu\t%s\n", bh(a).c_str(), sh, bh(a.shr(sh)).c_str());
    std::printf("B\tcmp\t%s\t%s\t%d\n", bh(a).c_str(), bh(b).c_str(), Big::cmp(a, b));
    std::printf("B\tbits\t%s\t%zu\n", bh(a).c_str(), a.bits());
    const size_t n = rnd() % 260;
    std::printf("B\tany\t%s\t%zu\t%d\n", bh(a).c_str(), n, (int)a.any_below(n));
    if (a.fits_u64())
      std::printf("B\ttou64\t%s\t%llu\n", bh(a).c_str(), (unsigned long long)a.to_u64());
  }

  // Real.
  for (int i = 0; i < 120; i++) {
    Real a = rreal(), b = rreal();
    if (b.zero()) b = Real(1);
    std::printf("R\tadd\t%s\t%s\t%s\t%s\n", rh(a).c_str(), rh(b).c_str(),
                rh(Real::add(a, b, Dir::DOWN)).c_str(), rh(Real::add(a, b, Dir::UP)).c_str());
    if (!(a < b))
      std::printf("R\tsub\t%s\t%s\t%s\t%s\n", rh(a).c_str(), rh(b).c_str(),
                  rh(Real::sub(a, b, Dir::DOWN)).c_str(), rh(Real::sub(a, b, Dir::UP)).c_str());
    else
      std::printf("R\tsub\t%s\t%s\t%s\t%s\n", rh(b).c_str(), rh(a).c_str(),
                  rh(Real::sub(b, a, Dir::DOWN)).c_str(), rh(Real::sub(b, a, Dir::UP)).c_str());
    std::printf("R\tmul\t%s\t%s\t%s\t%s\n", rh(a).c_str(), rh(b).c_str(),
                rh(Real::mul(a, b, Dir::DOWN)).c_str(), rh(Real::mul(a, b, Dir::UP)).c_str());
    std::printf("R\tdiv\t%s\t%s\t%s\t%s\n", rh(a).c_str(), rh(b).c_str(),
                rh(Real::div(a, b, Dir::DOWN)).c_str(), rh(Real::div(a, b, Dir::UP)).c_str());
    std::printf("R\tsqrt\t%s\t%s\t%s\n", rh(a).c_str(), rh(Real::sqrt(a, Dir::DOWN)).c_str(),
                rh(Real::sqrt(a, Dir::UP)).c_str());
    const u64 e = rnd() % 7;
    std::printf("R\tpow\t%s\t%llu\t%s\t%s\n", rh(a).c_str(), (unsigned long long)e,
                rh(Real::pow(a, e, Dir::DOWN)).c_str(), rh(Real::pow(a, e, Dir::UP)).c_str());
    std::printf("R\tfloor\t%s\t%s\n", rh(a).c_str(), bh(a.floor()).c_str());
    std::printf("R\tceil\t%s\t%s\n", rh(a).c_str(), bh(a.ceil()).c_str());
    std::printf("R\ttop\t%s\t%ld\n", rh(a).c_str(), a.top());
    if (!a.zero()) {
      const double x = bits_of(a);
      std::printf("R\tcut2\t%s\t%.17g\t%.2f\n", rh(a).c_str(), x, cut2(x));
    }
  }

  // Bound.
  for (int i = 0; i < 100; i++) {
    Real a = rpos(), b = rpos();
    Bound x(Real(a), Real::add(a, b, Dir::UP));
    Real c = rpos();
    Bound y(Real(c), Real::add(c, Real(1), Dir::UP));
    std::printf("D\tadd\t%s\t%s\t%s\n", dh(x).c_str(), dh(y).c_str(), dh(x + y).c_str());
    std::printf("D\tmul\t%s\t%s\t%s\n", dh(x).c_str(), dh(y).c_str(), dh(x * y).c_str());
    if (!y.lo.zero())
      std::printf("D\tdiv\t%s\t%s\t%s\n", dh(x).c_str(), dh(y).c_str(), dh(x / y).c_str());
    std::printf("D\tsub\t%s\t%s\t%s\n", dh(y).c_str(), dh(x).c_str(), dh(y - x).c_str());
    std::printf("D\tsqrt\t%s\t%s\n", dh(x).c_str(), dh(Bound::sqrt(x)).c_str());
    const u64 e = rnd() % 5;
    std::printf("D\tpow\t%s\t%llu\t%s\n", dh(x).c_str(), (unsigned long long)e,
                dh(Bound::pow(x, e)).c_str());
    std::printf("D\terr\t%s\t%s\n", dh(x).c_str(), rh(x.error()).c_str());
    std::printf("D\tsurely_le\t%s\t%s\t%d\n", dh(x).c_str(), dh(y).c_str(), (int)surely_le(x, y));
    std::printf("D\tsurely_lt\t%s\t%s\t%d\n", dh(x).c_str(), dh(y).c_str(), (int)surely_lt(x, y));
  }

  // Codes.
  const Setting s = setting_goldilocks();
  for (int i = 0; i < 40; i++) {
    CodeSize c;
    c.log_n = 6 + (unsigned)(rnd() % 8);
    c.ell = 8 + rnd() % 200;
    c.r = rnd() % 40;
    c.over_E = false;
    const bool circle = (rnd() & 1) != 0;
    Setting sc = s;
    sc.circle = circle;
    if (c.k(sc) >= c.n()) continue;
    std::printf("C\thidden\t%u\t%llu\t%llu\t%d\t%llu\t%llu\n", c.log_n,
                (unsigned long long)c.ell, (unsigned long long)c.r, (int)circle,
                (unsigned long long)hidden_positions(sc, c), (unsigned long long)tail_for(sc, c.r));
    const Word w = word_of(sc, c);
    std::printf("C\trho\t%u\t%llu\t%llu\t%d\t%s\n", c.log_n, (unsigned long long)c.ell,
                (unsigned long long)c.r, (int)circle, dh(rho_of(w)).c_str());
    const u64 m = 3 + rnd() % 60;
    const Proximity j = johnson(w, m);
    std::printf("C\tjohnson\t%u\t%llu\t%llu\t%d\t%llu\t%s\t%s\t%s\t%s\t%s\t%d\n", c.log_n,
                (unsigned long long)c.ell, (unsigned long long)c.r, (int)circle,
                (unsigned long long)j.m, dh(j.agree).c_str(), dh(j.delta).c_str(),
                dh(j.eta).c_str(), dh(j.count).c_str(), bh(j.list).c_str(), (int)j.source);
    const Real agree = Real::div(Real(Big(c.k(sc))), Real(Big(c.n())), Dir::UP);
    const Proximity at = at_distance(w, Bound(agree));
    std::printf("C\tat\t%u\t%llu\t%llu\t%d\t%s\t%s\t%s\t%s\t%s\t%s\t%d\t%d\n", c.log_n,
                (unsigned long long)c.ell, (unsigned long long)c.r, (int)circle, rh(agree).c_str(),
                dh(at.agree).c_str(), dh(at.delta).c_str(), dh(at.eta).c_str(),
                dh(at.count).c_str(), bh(at.list).c_str(), (int)at.m, (int)at.source);
    std::printf("C\tmca\t%llu\t%s\n", (unsigned long long)m, dh(mca_error(sc, j)).c_str());
    const Bound extra(Real(1), Real::add(Real(1), Real(1), Dir::UP));
    std::printf("C\tpos\t%s\t%u\t%s\t%llu\t%llu\n", rh(agree).c_str(), 100u, dh(extra).c_str(),
                (unsigned long long)3, (unsigned long long)positions(Bound(agree), 100, extra, 3));
    std::printf("C\tfielderr\t%u\t%llu\t%s\n", 0u, 100ull, dh(field_error(sc, 100)).c_str());
    std::printf("C\tfielderr\t%u\t%llu\t%s\n", 1u, 100ull, dh(field_error_nonzero(sc, 100)).c_str());
    const Big list = Big(10 + rnd() % 1000);
    std::printf("C\tsample\t%s\t%u\t%u\t%d\t%s\n", bh(list).c_str(), 10u, 1u, (int)circle,
                dh(sample_error(sc, list, 10, 1)).c_str());
  }
  std::printf("C\tlargest\t%llu\t%llu\n", 100ull,
              (unsigned long long)largest_m([](u64 m) { return m >= 5 && m <= 20; }, 100));
  return 0;
}
