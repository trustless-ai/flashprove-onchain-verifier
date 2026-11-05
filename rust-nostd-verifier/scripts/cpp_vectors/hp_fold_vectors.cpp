// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for blocks/iop/{hp,fold_algebra,fold_rounds}.h. Build with
// `clang++ -O2 -std=c++17 -Iblocks -DBLK_FIELD=2`.

#include "field/field.h"
#include "iop/fold_algebra.h"
#include "iop/fold_rounds.h"
#include "iop/hp.h"

#include <cstdio>
#include <vector>

using namespace blk;

namespace {
void pv(F x) { std::printf("%016llx", (unsigned long long)x.v); }
void pv(E x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
template <class K> void plist(const char *name, const std::vector<K> &v) {
  std::printf("%s=", name);
  if (v.empty()) std::printf("-");
  for (size_t i = 0; i < v.size(); i++) {
    if (i) std::printf(";");
    pv(v[i]);
  }
}
template <class K> void pweight(const char *tag, const Weight<K> &w) {
  std::printf("%s d=%u ", tag, w.d);
  plist("moment", w.moment);
  std::printf(" ");
  plist("psi", w.psi);
  std::printf(" fixed=%u finv=", w.fixed);
  pv(w.fixed_inv);
  std::printf("\n");
}
template <class K, class Make> void field_vectors(const char *name, Make mk) {
  std::printf("FIELD %s\n", name);
  const Weight<K> plain = Weight<K>::plain(3);
  const Weight<K> eq = Weight<K>::equality(mk(7), 3);
  const Weight<K> at0 = Weight<K>::at_zero(3);
  const Weight<K> lag = Weight<K>::lagrange({mk(0), mk(1), mk(3)}, mk(5), 4);
  pweight("W plain", plain);
  pweight("W eq", eq);
  pweight("W at0", at0);
  pweight("W lag", lag);
  std::vector<K> g = {mk(10), mk(11), mk(12), mk(13)};
  std::vector<K> g3 = {mk(10), mk(11), mk(12)};
  std::printf("APPLY plain ");
  plist("g", g3);
  std::printf(" r=");
  pv(plain.apply(g3));
  std::printf(" of_one=");
  pv(plain.of_one());
  std::printf("\n");
  std::vector<K> q = {mk(20), mk(21), mk(22)};
  Weight<K> plain3 = Weight<K>::plain(3);
  plain3.complete(q, mk(23));
  std::printf("COMPLETE claim=");
  pv(mk(23));
  std::printf(" ");
  plist("q", q);
  std::printf("\n");

  std::vector<Weight<K>> vars = {Weight<K>::plain(3), Weight<K>::equality(mk(8), 3), Weight<K>::plain(4)};
  std::vector<K> entries;
  for (size_t i = 0; i < hp_entries(vars); i++) entries.push_back(mk(100 + i));
  HidingPolynomial<K> U(vars, entries);
  std::printf("HP entries=%zu sum=", hp_entries(vars));
  pv(U.sum());
  std::printf("\n");
  for (size_t j = 0; j < vars.size(); j++) {
    std::vector<K> r = U.round();
    std::printf("HPROUND i=%zu ", j);
    plist("q", r);
    std::printf("\n");
    U.bind(g[j]);
    std::printf("HPBIND i=%zu g=", j);
    pv(g[j]);
    std::printf("\n");
  }
  std::printf("HPVALUE ");
  pv(U.value());
  std::printf("\n");
  std::printf("HPFORM k=%zu ", vars.size());
  plist("gamma", g3);
  std::printf(" ");
  plist("form", hp_form(vars, g3));
  std::printf("\n");
  std::printf("HPPLACE ");
  {
    bool first = true;
    for (size_t l = 0; l < vars.size(); l++)
      for (size_t t = 0; t < vars[l].d; t++) {
        if (l + 1 != vars.size() && t == 0) continue;
        std::printf("%s%zu", first ? "" : ",", hp_place(vars, l, t));
        first = false;
      }
  }
  std::printf("\n");

  std::printf("POLYAT ");
  plist("g", std::vector<K>{mk(1), mk(2), mk(3)});
  std::printf(" x=");
  pv(mk(9));
  std::printf(" r=");
  pv(poly_at({mk(1), mk(2), mk(3)}, mk(9)));
  std::printf("\n");
  std::vector<K> vals = {mk(30), mk(31), mk(34), mk(41)};
  std::vector<K> interp = poly_from_values_at_0_1_2(vals);
  std::printf("POLYINTERP ");
  plist("values", vals);
  std::printf(" ");
  plist("coeffs", interp);
  std::printf("\n");

  std::vector<K> fl = {mk(50), mk(51), mk(52), mk(53), mk(54), mk(55), mk(56), mk(57)};
  std::vector<K> fl1 = fl;
  fold_low_once(fl1, mk(60));
  std::printf("FOLDLOWONCE ");
  plist("v", fl);
  std::printf(" g=");
  pv(mk(60));
  std::printf(" ");
  plist("out", fl1);
  std::printf("\n");
  std::printf("FOLDLOW ");
  plist("v", fl);
  std::printf(" ");
  plist("g", std::vector<K>{mk(60), mk(61), mk(62)});
  std::printf(" ");
  plist("out", fold_low(fl, std::vector<K>{mk(60), mk(61), mk(62)}.data(), 3));
  std::printf("\n");
  std::vector<K> a = {mk(70), mk(71), mk(72), mk(73), mk(74), mk(75), mk(76), mk(77)};
  std::vector<K> m = {mk(80), mk(81), mk(82), mk(83), mk(84), mk(85), mk(86), mk(87)};
  std::printf("PAIRPRODUCTS ");
  plist("a", a);
  std::printf(" ");
  plist("m", m);
  std::printf(" ");
  plist("q", pair_products(a, m));
  std::printf("\n");
  std::printf("INNER ");
  plist("a", std::vector<K>{mk(90), mk(91), mk(92), mk(93)});
  std::printf(" ");
  plist("b", std::vector<K>{mk(94), mk(95), mk(96), mk(97)});
  std::printf(" r=");
  pv(inner(std::vector<K>{mk(90), mk(91), mk(92), mk(93)}, std::vector<K>{mk(94), mk(95), mk(96), mk(97)}));
  std::printf("\n");
}
} // namespace

int main() {
  field_vectors<F>("F", [](u64 x) { return F{x}; });
  field_vectors<E>("E", [](u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; });

  auto e = [](u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; };
  std::vector<E> w7;
  for (u64 i = 0; i < 7; i++) w7.push_back(e(200 + i));
  for (unsigned k : {3u, 2u}) {
    std::vector<E> wk;
    for (u64 i = 0; i < 2 * u64(k) + 1; i++) wk.push_back(e(200 + i));
    std::vector<E> gk;
    for (unsigned i = 0; i < k; i++) gk.push_back(e(10 + i));
    for (unsigned h = 1; h <= k; h++) {
      const size_t len = fold_mask_columns(k, h);
      std::printf("MASKTABLE k=%u h=%u len=%zu ", k, h, len);
      plist("w", wk);
      std::printf(" ");
      plist("table", fold_mask_table(k, h, len, wk));
      std::printf("\n");
      std::printf("MASKWEIGHTS k=%u h=%u len=%zu ", k, h, len);
      plist("g", gk);
      std::printf(" ");
      plist("u", fold_mask_weights(k, h, len, gk));
      std::printf("\n");
    }
  }

  const unsigned k = 3, h = 2;
  const size_t len = fold_mask_columns(k, h);
  std::vector<E> d, mu;
  for (u64 i = 0; i < (u64(1) << h) * len; i++) d.push_back(e(300 + i)), mu.push_back(e(400 + i));
  std::vector<E> g = {e(10), e(11), e(12)};
  FoldProverRounds<E> pr(k, h, len, w7, d, mu, e(500));
  std::printf("FOLDPROVER k=%u h=%u len=%zu mask_sum=", k, h, len);
  pv(pr.mask_sum());
  std::printf("\n");
  pr.start(e(501));
  FoldVerifierRounds<E> vr(pr.mask_sum(), e(501), e(502));
  for (unsigned j = 0; j < k; j++) {
    std::vector<E> main = {e(600 + 3 * j), e(601 + 3 * j), e(602 + 3 * j)};
    std::vector<E> q = pr.round(main);
    std::printf("FOLDQ i=%u ", j);
    plist("main", main);
    std::printf(" ");
    plist("q", q);
    std::printf("\n");
    pr.bind(g[j]);
    std::printf("FOLDBIND i=%u g=", j);
    pv(g[j]);
    std::printf("\n");
    vr.round(q[0], q[2], g[j]);
    std::printf("FOLDVCLAIM i=%u claim=", j);
    pv(vr.claim());
    std::printf("\n");
  }
  FoldMaskEnd<E> end = pr.end(true);
  std::printf("FOLDEND ");
  plist("d", end.d);
  std::printf(" ");
  plist("mu", end.mu);
  std::printf(" ");
  plist("fresh", end.fresh);
  std::printf("\n");
  std::printf("FOLDMASKFORM k=%u h=%u ", k, h);
  plist("d", d);
  std::printf(" eps=");
  pv(e(700));
  std::printf(" ");
  plist("g", g);
  std::printf(" ");
  plist("out", fold_mask_form(k, h, d, e(700), g));
  std::printf("\n");
  std::printf("KEPTFACTOR eps=");
  pv(e(701));
  std::printf(" ");
  plist("g", g);
  std::printf(" s=");
  pv(fold_kept_factor(e(701), g));
  std::printf("\n");
  return 0;
}
