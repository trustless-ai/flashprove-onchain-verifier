// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Prints the two hash-call counters of C++ for fixed input sequences, so that the Rust port can
// compare `HashCalls::f2b` and `HashCalls::blk` on the same sequence. Build with
// -DBLK_COUNT_HASH_CALLS=1 (and -DBLK_FIELD=2 for blocks/).

#include "vf_earlier_hash.h"

#include "hash/hash.h"

#include <cstdio>
#include <cstring>
#include <vector>

using namespace blk;

namespace {
constexpr size_t THPW = 16 * 8;

void reset() {
  f2b::calls_begin("counters");
#if BLK_COUNT_HASH_CALLS
  hash_calls_made.store(0, std::memory_order_relaxed);
#endif
}

void print(const char *group) {
  std::printf("COUNTS %s %llu %llu\n", group, (unsigned long long)f2b::calls_total(),
#if BLK_COUNT_HASH_CALLS
              (unsigned long long)hash_calls_counted());
#else
              0ull);
#endif
}

void th_digest(const std::vector<u32> &w, u32 out[8]) {
  std::vector<u32> cur = w;
  u32 num = 10;
  for (;;) {
    const size_t nc = (cur.size() + THPW - 1) / THPW;
    std::vector<u32> nx(8 * nc);
    for (size_t i = 0; i < nc; i++) {
      const size_t take = cur.size() - THPW * i < THPW ? cur.size() - THPW * i : THPW;
      earlier_hash_h_digest(nx.data() + 8 * i, num, cur.data() + THPW * i, take);
    }
    if (nx.size() == 8) {
      std::memcpy(out, nx.data(), 32);
      return;
    }
    cur.swap(nx);
    num = 11;
  }
}
} // namespace

int main() {
  const size_t h_lengths[] = {0, 1, 7, 8, 127, 128, 129, 1000};
  const u32 nums[] = {3, 10, 107};
  const size_t th_lengths[] = {8, 127, 128, 129, 1000};
  const size_t block_lengths[] = {0, 1, 127, 128, 129, 1000};

  reset();
  for (size_t n : h_lengths) {
    std::vector<u32> w(n);
    for (size_t k = 0; k < n; k++) w[k] = (u32)((k + 1) * 0x89ABCDEFu);
    for (u32 num : nums) {
      u32 d[8];
      earlier_hash_h_digest(d, num, w.data(), n);
    }
  }
  print("H");

  reset();
  for (size_t n : th_lengths) {
    std::vector<u32> w(n);
    for (size_t k = 0; k < n; k++) w[k] = (u32)((k + 1) * 0x89ABCDEFu);
    u32 d[8];
    th_digest(w, d);
  }
  print("TH");

  reset();
  for (size_t n : block_lengths) {
    std::vector<u8> data(n);
    for (size_t i = 0; i < n; i++) data[i] = (u8)(7 * i + 3);
    Hasher h(Domain::STATEMENT, 1);
    h.push(data.data(), data.size());
    h.finish();
  }
  print("BLOCKS");

  reset();
  {
    std::vector<u32> w(129);
    for (size_t k = 0; k < w.size(); k++) w[k] = (u32)((k + 1) * 0x89ABCDEFu);
    u32 d[8];
    earlier_hash_h_digest(d, 10, w.data(), w.size());
  }
  {
    std::vector<u8> data(129);
    for (size_t i = 0; i < data.size(); i++) data[i] = (u8)(7 * i + 3);
    Hasher h(Domain::STATEMENT, 1);
    h.push(data.data(), data.size());
    h.finish();
  }
  print("MIXED");
  return 0;
}
