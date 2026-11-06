// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Generates deterministic test vectors for the Rust port of blocks/field/{gl64,field,mle}.h.
// This is an independent tool: it includes the C++ headers and changes no source of theirs.
// Build (from the repository root):
//   clang++ -O2 -std=c++17 -Iblocks -DBLK_FIELD=2 -o /tmp/field_vectors \
//     rust-verifier/scripts/cpp_vectors/field_vectors.cpp
// The output is line-oriented and is compared with fp-host/tests/field_vectors.rs.

#include "field/field.h"
#include "field/mle.h"

#include <cstdio>
#include <vector>

using namespace blk;

namespace {
u64 state = 1;
u64 word() {
  u64 z = (state += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}
F rf() {
  F x;
  while (!F_from_word(word(), x)) {
  }
  return x;
}
E re() {
  return E::from(rf(), rf(), rf());
}
void hx(u64 v) {
  std::printf("%016llx", (unsigned long long)v);
}
void hf(F x) {
  hx(x.v);
}
void he(const E &x) {
  hf(x.c[0]);
  std::printf(" ");
  hf(x.c[1]);
  std::printf(" ");
  hf(x.c[2]);
}
void pf2(const char *op, F a, F b, F r) {
  std::printf("F %s ", op);
  hf(a);
  std::printf(" ");
  hf(b);
  std::printf(" ");
  hf(r);
  std::printf("\n");
}
void pf1(const char *op, F a, F r) {
  std::printf("F %s ", op);
  hf(a);
  std::printf(" ");
  hf(r);
  std::printf("\n");
}
void pe2(const char *op, const E &a, const E &b, const E &r) {
  std::printf("E %s ", op);
  he(a);
  std::printf(" ");
  he(b);
  std::printf(" ");
  he(r);
  std::printf("\n");
}
void pe1(const char *op, const E &a, const E &r) {
  std::printf("E %s ", op);
  he(a);
  std::printf(" ");
  he(r);
  std::printf("\n");
}
} // namespace

int main() {
  std::vector<u64> edge = {0, 1, 2, 3, 7, 8, P - 1, P - 2, P / 2, P / 2 + 1, P / 3,
                           (1ull << 32) - 1, 1ull << 32, (1ull << 32) + 1, 1ull << 63,
                           (1ull << 63) - 1, 0xFFFFFFFF00000000ull, 0xFFFFFFFE00000001ull};
  for (u64 &v : edge) v %= P;
  for (int i = 0; i < 8; i++) edge.push_back(rf().v);

  // Base-field arithmetic: edge pairs, then random pairs.
  for (size_t i = 0; i < edge.size(); i++)
    for (size_t j = 0; j < edge.size(); j++) {
      const F a{edge[i]}, b{edge[j]};
      pf2("add", a, b, a + b);
      pf2("sub", a, b, a - b);
      pf2("mul", a, b, a * b);
    }
  for (int i = 0; i < 200; i++) {
    const F a = rf(), b = rf();
    pf2("add", a, b, a + b);
    pf2("sub", a, b, a - b);
    pf2("mul", a, b, a * b);
  }
  for (size_t i = 0; i < edge.size(); i++) {
    const F a{edge[i]};
    pf1("neg", a, -a);
    pf1("inv", a, inv(a));
    pf1("pow0", a, pow(a, 0));
    pf1("pow1", a, pow(a, 1));
    pf1("pow5", a, pow(a, 5));
    pf1("powP", a, pow(a, P));
    std::printf("F from_u64 ");
    hx(edge[i]);
    std::printf(" ");
    hf(from_u64(edge[i]));
    std::printf("\n");
  }
  for (int i = 0; i < 200; i++) {
    const F a = rf();
    pf1("inv", a, inv(a));
    pf1("pow5", a, pow(a, 5));
    pf1("powP", a, pow(a, P));
  }
  for (i64 v : {(i64)0, (i64)1, (i64)-1, (i64)5, (i64)-5, (i64)INT64_MAX, (i64)INT64_MIN, (i64)(INT64_MIN + 1),
                (i64)1 << 61, -((i64)1 << 61)}) {
    std::printf("F from_i64 ");
    hx((u64)v);
    std::printf(" ");
    hf(from_i64(v));
    std::printf("\n");
  }
  // reduce128 and dot3.
  for (u64 hi : {0ull, 1ull, ~0ull, ~0ull - 1, 0xFFFFFFFFull, 0xFFFFFFFF00000000ull, 1ull << 63, 1ull << 58})
    for (u64 lo : {0ull, 1ull, ~0ull, ~0ull - 1, 0xFFFFFFFFull, 0xFFFFFFFF00000001ull, 1ull << 61})
      std::printf("F reduce128 %016llx %016llx %016llx\n", (unsigned long long)hi, (unsigned long long)lo,
                  (unsigned long long)BaseField::reduce128(hi, lo));
  for (int i = 0; i < 200; i++) {
    const u64 hi = word(), lo = word();
    std::printf("F reduce128 %016llx %016llx %016llx\n", (unsigned long long)hi, (unsigned long long)lo,
                (unsigned long long)BaseField::reduce128(hi, lo));
  }
  for (int i = 0; i < 200; i++) {
    const F a = rf(), b = rf(), c = rf(), d = rf(), e = rf(), f = rf();
    std::printf("F dot3 %016llx %016llx %016llx %016llx %016llx %016llx %016llx\n",
                (unsigned long long)a.v, (unsigned long long)b.v, (unsigned long long)c.v,
                (unsigned long long)d.v, (unsigned long long)e.v, (unsigned long long)f.v,
                (unsigned long long)BaseField::dot3(a.v, b.v, c.v, d.v, e.v, f.v));
  }

  // Extension field.
  std::vector<E> ee;
  for (u64 a : {0ull, 1ull, P - 1, P - 2, P / 2})
    for (u64 b : {0ull, 1ull, P - 1})
      for (u64 c : {0ull, 1ull, P - 1}) ee.push_back(E::from(F{a}, F{b}, F{c}));
  for (int i = 0; i < 20; i++) ee.push_back(re());
  for (size_t i = 0; i < ee.size(); i++)
    for (size_t j = 0; j < ee.size(); j++) {
      const E a = ee[i], b = ee[j];
      pe2("add", a, b, a + b);
      pe2("sub", a, b, a - b);
      pe2("mul", a, b, a * b);
    }
  for (int i = 0; i < 200; i++) {
    const E a = re(), b = re();
    pe2("add", a, b, a + b);
    pe2("sub", a, b, a - b);
    pe2("mul", a, b, a * b);
    pe2("mulf", a, b, a * b.c[1]);
  }
  for (const E &a : ee) {
    pe1("neg", a, -a);
    pe1("inv", a, inv(a));
    pe1("pow0", a, pow(a, 0));
    pe1("pow3", a, pow(a, 3));
    pe1("powP", a, pow(a, P));
  }
  for (int i = 0; i < 200; i++) {
    const E a = re();
    pe1("inv", a, inv(a));
    pe1("powP", a, pow(a, P));
  }
  for (unsigned i = 0; i < 5; i++) {
    const E a = E::theta(i);
    std::printf("E theta %u ", i);
    he(a);
    std::printf("\n");
  }

  // Multilinear helpers.
  for (unsigned k = 0; k <= 6; k++) {
    const size_t n = (size_t)1 << k;
    std::vector<E> z(k), w(k), ve(n), out_e(n);
    std::vector<F> vf(n), f(k), out_f(n);
    for (auto &x : z) x = re();
    for (auto &x : w) x = re();
    for (auto &x : ve) x = re();
    for (auto &x : vf) x = rf();
    for (auto &x : f) x = rf();

    eq_table(z.data(), k, out_e.data());
    std::printf("MLE eq_table %u", k);
    for (const auto &x : z) {
      std::printf(" ");
      he(x);
    }
    for (const auto &x : out_e) {
      std::printf(" ");
      he(x);
    }
    std::printf("\n");

    for (u64 j : {0ull, 1ull, (u64)(n / 2), (u64)(n - 1), (u64)(n + 3)}) {
      std::printf("MLE eq_index %u %llu", k, (unsigned long long)j);
      for (const auto &x : z) {
        std::printf(" ");
        he(x);
      }
      std::printf(" ");
      he(eq_index(j, z.data(), k));
      std::printf("\n");
    }
    std::printf("MLE eq_eval %u ", k);
    for (const auto &x : z) {
      he(x);
      std::printf(" ");
    }
    for (const auto &x : w) {
      he(x);
      std::printf(" ");
    }
    he(eq_eval(z.data(), w.data(), k));
    std::printf("\n");

    {
      std::vector<E> coeff = {re(), re(), re(), re(), re()};
      const E x = re();
      std::printf("MLE poly_eval 5 ");
      he(x);
      for (const auto &c : coeff) {
        std::printf(" ");
        he(c);
      }
      std::printf(" ");
      he(poly_eval(coeff.data(), coeff.size(), x));
      std::printf("\n");
      std::printf("MLE poly_eval 0 ");
      he(x);
      std::printf(" ");
      he(poly_eval(coeff.data(), 0, x));
      std::printf("\n");
    }

    std::printf("MLE mle_eval_F %u 0", k);
    for (const auto &x : z) {
      std::printf(" ");
      he(x);
    }
    std::printf(" ");
    he(mle_eval(vf.data(), 0, z.data(), k));
    std::printf("\n");
    for (size_t len : {n, (size_t)1}) {
      if (len > n) continue;
      std::printf("MLE mle_eval_F %u %zu", k, len);
      for (const auto &x : z) {
        std::printf(" ");
        he(x);
      }
      for (size_t i = 0; i < len; i++) {
        std::printf(" ");
        hf(vf[i]);
      }
      std::printf(" ");
      he(mle_eval(vf.data(), len, z.data(), k));
      std::printf("\n");
      std::printf("MLE mle_eval_E %u %zu", k, len);
      for (const auto &x : z) {
        std::printf(" ");
        he(x);
      }
      for (size_t i = 0; i < len; i++) {
        std::printf(" ");
        he(ve[i]);
      }
      std::printf(" ");
      he(mle_eval(ve.data(), len, z.data(), k));
      std::printf("\n");
    }

    product_table(f.data(), k, n, out_f.data());
    std::printf("MLE product_table %u %zu", k, n);
    for (const auto &x : f) {
      std::printf(" ");
      hf(x);
    }
    for (const auto &x : out_f) {
      std::printf(" ");
      hf(x);
    }
    std::printf("\n");
    for (u64 j : {0ull, 1ull, (u64)(n / 2), (u64)(n - 1), (u64)(n + 3)}) {
      std::printf("MLE product_index %u %llu", k, (unsigned long long)j);
      for (const auto &x : f) {
        std::printf(" ");
        hf(x);
      }
      std::printf(" ");
      hf(product_index(f.data(), k, j));
      std::printf("\n");
    }
    std::printf("MLE product_mle %u", k);
    for (const auto &x : f) {
      std::printf(" ");
      hf(x);
    }
    for (const auto &x : z) {
      std::printf(" ");
      he(x);
    }
    std::printf(" ");
    he(product_mle(f.data(), z.data(), k));
    std::printf("\n");

    for (size_t len : {n, (size_t)1}) {
      if (len > n) continue;
      std::printf("MLE product_dot_F %u %zu", k, len);
      for (const auto &x : f) {
        std::printf(" ");
        hf(x);
      }
      for (size_t i = 0; i < len; i++) {
        std::printf(" ");
        hf(vf[i]);
      }
      std::printf(" ");
      hf(product_dot(vf.data(), len, f.data(), k));
      std::printf("\n");
      std::printf("MLE product_dot_E %u %zu", k, len);
      for (const auto &x : f) {
        std::printf(" ");
        hf(x);
      }
      for (size_t i = 0; i < len; i++) {
        std::printf(" ");
        he(ve[i]);
      }
      std::printf(" ");
      he(product_dot(ve.data(), len, f.data(), k));
      std::printf("\n");
    }
  }
  return 0;
}
