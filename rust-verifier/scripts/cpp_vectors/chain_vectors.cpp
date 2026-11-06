// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for chain.h: the first query, rounds with and without work, the draws of a verifier's
// message, the fast path of the first element, and the record seeds. Build with
// -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1. The Rust test replays every line.

#include "chain/chain.h"
#include "chain/rounds.h"
#include "hash/hash.h"

#include <cstdio>
#include <vector>

using namespace blk;

namespace {
Digest make_digest(u32 seed) {
  Digest d{};
  for (int i = 0; i < 8; i++) d.w[i] = seed * 0x9E3779B9u + (u32)i * 0x85EBCA6Bu;
  return d;
}
void pd(const char *name, const Digest &d) {
  std::printf("%s=", name);
  for (int i = 0; i < 8; i++) std::printf("%08x", d.w[i]);
}
void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
void pe(const char *name, const E &x) {
  std::printf("%s=", name);
  pv(x);
}
void pbytes(const std::vector<u8> &b) {
  if (b.empty()) std::printf("-");
  for (u8 x : b) std::printf("%02x", x);
}
void pwords(const std::vector<u64> &w) {
  std::printf("words=");
  if (w.empty()) std::printf("-");
  for (size_t i = 0; i < w.size(); i++) std::printf("%s%llx", i ? "," : "", (unsigned long long)w[i]);
}
void reset() {
#if BLK_COUNT_HASH_CALLS
  hash_calls_made.store(0, std::memory_order_relaxed);
#endif
}
unsigned long long calls() {
#if BLK_COUNT_HASH_CALLS
  return (unsigned long long)hash_calls_counted();
#else
  return 0;
#endif
}
void chain_line(const FirstQuery &q, const Chain &c) {
  std::printf("CHAIN label=%llx salted=%d ", (unsigned long long)q.label, (int)q.salted);
  pd("params", q.parameters);
  std::printf(" statement=");
  if (q.statement.empty()) std::printf("-");
  for (u8 b : q.statement) std::printf("%02x", b);
  std::printf(" record=");
  if (q.record.empty()) std::printf("-");
  for (u8 b : q.record) std::printf("%02x", b);
  pd(" salt", q.salt);
  pd(" rho", c.value());
  std::printf(" rounds=%llu calls=%llu\n", (unsigned long long)c.rounds(), calls());
}
void round_line(int i, ChainKind k, unsigned work, u64 nonce, const std::vector<u64> &w, const Chain &c) {
  std::printf("ROUND i=%d kind=%u work=%u nonce=%llx ", i, (unsigned) k, work, (unsigned long long)nonce);
  pwords(w);
  pd(" rho", c.value());
  std::printf(" rounds=%llu calls=%llu\n", (unsigned long long)c.rounds(), calls());
}
u64 do_round(Chain &c, ChainKind k, const std::vector<u64> &w, unsigned work) {
  ChainAbsorb m = c.message();
  for (u64 x : w) m.push_u64(x);
  const ChainPrefix p = Chain::prefix(m, k, work);
  const u64 before = calls();
  u64 nonce = 0;
  if (work) nonce = search_nonce(p, work);
#if BLK_COUNT_HASH_CALLS
  hash_calls_made.store(before, std::memory_order_relaxed); // the prover's search is not a verifier's call
#endif
  const bool ok = c.step(p, nonce, work);
  std::printf("STEP ok=%d\n", (int)ok);
  return nonce;
}
void draw_e_line(int i, const E &x) {
  std::printf("DRAW_E i=%d ", i);
  pe("x", x);
  std::printf(" calls=%llu\n", calls());
}
void draw_f_line(int i, F x) {
  std::printf("DRAW_F i=%d x=%016llx calls=%llu\n", i, (unsigned long long)x.v, calls());
}
void pos_line(int i, unsigned log_n, u64 p) {
  std::printf("POS i=%d log_n=%u p=%llu calls=%llu\n", i, log_n, (unsigned long long)p, calls());
}
void bits_line(int i, const std::vector<signed char> &t) {
  std::printf("BITS i=%d n=%zu v=", i, t.size());
  for (size_t j = 0; j < t.size(); j++) std::printf("%s%d", j ? "," : "", (int)t[j]);
  std::printf(" calls=%llu\n", calls());
}
} // namespace

int main() {
  // Case 0: a salted chain, every kind of round, one round with work, long messages, draws past
  // the first four words of an answer.
  {
    FirstQuery q;
    q.label = 0x0123456789ABull;
    q.parameters = make_digest(1);
    q.statement = {1, 2, 3, 4, 5};
    q.record = {9, 9};
    q.salt = make_digest(2);
    reset();
    Chain c(q);
    std::printf("CASE 0\n");
    chain_line(q, c);
    {
      const std::vector<u64> w = {11, 22, 33, 44, 55};
      const u64 n = do_round(c, ChainKind::ALGEBRAIC, w, 0);
      round_line(0, ChainKind::ALGEBRAIC, 0, n, w, c);
      for (int i = 0; i < 2; i++) draw_e_line(i, c.draw_E());
      draw_e_line(2, c.draw_E_nonzero());
      draw_f_line(0, c.draw_F());
    }
    {
      const std::vector<u64> w;
      const u64 n = do_round(c, ChainKind::EMPTY, w, 0);
      round_line(1, ChainKind::EMPTY, 0, n, w, c);
      pos_line(0, 10, c.draw_position(10));
      pos_line(1, 10, c.draw_position(10));
    }
    {
      const std::vector<u64> w = {7};
      const u64 n = do_round(c, ChainKind::POSITIONS, w, 0);
      round_line(2, ChainKind::POSITIONS, 0, n, w, c);
      for (int i = 0; i < 3; i++) pos_line(i + 2, 8, c.draw_position(8));
      draw_e_line(3, c.draw_E());
    }
    {
      const std::vector<u64> w;
      const u64 n = do_round(c, ChainKind::BITS, w, 0);
      round_line(3, ChainKind::BITS, 0, n, w, c);
      std::vector<signed char> t(70, 0);
      for (size_t i = 0; i < t.size(); i += 32) {
        u64 x = c.next_word();
        for (size_t j = 0; j < 32 && i + j < t.size(); j++, x >>= 2)
          t[i + j] = (signed char)((int)(x & 1) - (int)(x & (x << 1) & 2));
      }
      bits_line(0, t);
    }
    {
      std::vector<u64> w;
      for (u64 i = 1; i <= 15; i++) w.push_back(i);
      const u64 n = do_round(c, ChainKind::ALGEBRAIC, w, 4);
      round_line(4, ChainKind::ALGEBRAIC, 4, n, w, c);
      draw_e_line(4, c.draw_E());
      draw_e_line(5, c.draw_E());
      draw_e_line(6, c.draw_E_nonzero());
    }
    {
      const std::vector<u64> w = {3};
      const u64 n = do_round(c, ChainKind::SEAL, w, 0);
      round_line(5, ChainKind::SEAL, 0, n, w, c);
      Digest d{};
      for (int i = 0; i < 4; i++) {
        const u64 x = c.next_word();
        d.w[2 * i] = (u32)x;
        d.w[2 * i + 1] = (u32)(x >> 32);
      }
      pd("SEAL", d);
      std::printf(" calls=%llu\n", calls());
    }
    pd("FINAL rho", c.value());
    std::printf(" rounds=%llu calls=%llu\n", (unsigned long long)c.rounds(), calls());
  }

  // Case 1: no salt, a short statement, an epsilon round and a long message.
  {
    FirstQuery q;
    q.label = 5;
    q.parameters = make_digest(3);
    q.salted = false;
    reset();
    Chain c(q);
    std::printf("CASE 1\n");
    chain_line(q, c);
    {
      const std::vector<u64> w = {123};
      const u64 n = do_round(c, ChainKind::EPSILON, w, 0);
      round_line(0, ChainKind::EPSILON, 0, n, w, c);
      draw_e_line(0, c.draw_E());
    }
    {
      const std::vector<u64> w;
      const u64 n = do_round(c, ChainKind::EMPTY, w, 0);
      round_line(1, ChainKind::EMPTY, 0, n, w, c);
      draw_f_line(0, c.draw_F());
      draw_f_line(1, c.draw_F());
    }
    {
      std::vector<u64> w;
      for (u64 i = 1; i <= 20; i++) w.push_back(i);
      const u64 n = do_round(c, ChainKind::ALGEBRAIC, w, 0);
      round_line(2, ChainKind::ALGEBRAIC, 0, n, w, c);
      draw_e_line(1, c.draw_E());
    }
    {
      const std::vector<u64> w = {17};
      const u64 n = do_round(c, ChainKind::SEAL, w, 0);
      round_line(3, ChainKind::SEAL, 0, n, w, c);
      Digest d{};
      for (int i = 0; i < 4; i++) {
        const u64 x = c.next_word();
        d.w[2 * i] = (u32)x;
        d.w[2 * i + 1] = (u32)(x >> 32);
      }
      pd("SEAL", d);
      std::printf(" calls=%llu\n", calls());
    }
    pd("FINAL rho", c.value());
    std::printf(" rounds=%llu calls=%llu\n", (unsigned long long)c.rounds(), calls());
  }

  // Case 2: the largest label, a 200-byte statement, many draws.
  {
    FirstQuery q;
    q.label = 0x0000FFFFFFFFFFFFull;
    q.parameters = make_digest(4);
    for (int i = 0; i < 200; i++) q.statement.push_back((u8)(i * 7 + 3));
    q.salt = make_digest(5);
    reset();
    Chain c(q);
    std::printf("CASE 2\n");
    chain_line(q, c);
    {
      std::vector<u64> w;
      for (u64 i = 1; i <= 30; i++) w.push_back(i);
      const u64 n = do_round(c, ChainKind::ALGEBRAIC, w, 0);
      round_line(0, ChainKind::ALGEBRAIC, 0, n, w, c);
      for (int i = 0; i < 3; i++) draw_e_line(i, c.draw_E());
      for (int i = 0; i < 3; i++) draw_f_line(i, c.draw_F());
    }
    {
      const std::vector<u64> w = {1};
      const u64 n = do_round(c, ChainKind::SEAL, w, 0);
      round_line(1, ChainKind::SEAL, 0, n, w, c);
      Digest d{};
      for (int i = 0; i < 4; i++) {
        const u64 x = c.next_word();
        d.w[2 * i] = (u32)x;
        d.w[2 * i + 1] = (u32)(x >> 32);
      }
      pd("SEAL", d);
      std::printf(" calls=%llu\n", calls());
    }
    pd("FINAL rho", c.value());
    std::printf(" rounds=%llu calls=%llu\n", (unsigned long long)c.rounds(), calls());
  }

  // The fast path of the first element of a verifier's message.
  {
    const u64 w0s[] = {0, 1, 0x123456789abcdefull, 0xFFFFFFFF00000001ull};
    const u64 w1s[] = {0, 2, 0xdeadbeefcafebabeull};
    const u64 w2s[] = {0, 3, 0x0f0f0f0f0f0f0f0full};
    int i = 0;
    for (u64 a : w0s)
      for (u64 b : w1s)
        for (u64 c : w2s) {
          for (int nz = 0; nz < 2; nz++) {
            E x = E::zero();
            const bool taken = draw_E_straight(a, b, c, nz != 0, x);
            std::printf("STRAIGHT i=%d w0=%016llx w1=%016llx w2=%016llx nz=%d ok=%d ", i++, (unsigned long long)a,
                        (unsigned long long)b, (unsigned long long)c, nz, (int)taken);
            pe("x", x);
            std::printf("\n");
          }
        }
  }

  // The seeds of a committed table's record.
  {
    const std::vector<u8> commitment = {0xde, 0xad, 0xbe, 0xef, 0x00, 0x11, 0x22};
    reset();
    const std::vector<SampleSeed> seeds = record_seeds(commitment.data(), commitment.size(), 3, 2);
    std::printf("SEEDS n=%zu commitment=", seeds.size());
    pbytes(commitment);
    std::printf(" calls=%llu\n", calls());
    for (size_t i = 0; i < seeds.size(); i++) {
      std::printf("SEED i=%zu ", i);
      pe("beta", seeds[i].beta);
      std::printf(" z=");
      for (size_t j = 0; j < seeds[i].z.size(); j++) {
        if (j) std::printf(";");
        pv(seeds[i].z[j]);
      }
      std::printf(" calls=%llu\n", calls());
    }
  }
  return 0;
}
