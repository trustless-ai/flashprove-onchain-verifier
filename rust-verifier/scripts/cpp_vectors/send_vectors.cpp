// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for SEND's sample claim (`Send::form`, send.h:205-227) and the cube/pad sizes that it
// uses. Build with -DBLK_FIELD=2.

#include "iop/send.h"

#include <cstdio>
#include <vector>

using namespace blk;

namespace {
E e(u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; }
void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
} // namespace

int main() {
  Codes codes;
  codes.base.push_back(Code{3, 4, 2});
  codes.mask.push_back(Code{2, 2, 1});
  Statement S(codes);
  OracleShape s;
  s.name = "send-shape";
  s.code = 0;
  s.main_rows = 2;
  s.main_deg = 1;
  s.mask_rows = 2;
  s.mask_code = 0;
  s.answers = 2;
  const OracleId o = S.sent(s);
  const SampleCube c = Send::cube(codes, s);
  std::printf("CUBE has_main=%d has_mask=%d main_row_bits=%u main_bits=%u mask_row_bits=%u mask_bits=%u bits=%u\n",
              (int)c.has_main, (int)c.has_mask, c.main_row_bits, c.main_bits, c.mask_row_bits, c.mask_bits, c.bits);
  std::printf("PAD");
  for (const PadPlace &p : Send::pad(codes, s))
    std::printf(" %u:%llu:%u", (unsigned)p.part, (unsigned long long)p.index, p.answer);
  std::printf("\n");

  SampleSeed seed;
  seed.z.resize(c.bits);
  for (unsigned i = 0; i < c.bits; i++) seed.z[i] = e(300 + i);
  seed.beta = e(400);
  std::printf("SEED z=");
  for (size_t i = 0; i < seed.z.size(); i++) {
    if (i) std::printf(";");
    pv(seed.z[i]);
  }
  std::printf(" beta=");
  pv(seed.beta);
  std::printf("\n");

  for (unsigned answer = 0; answer < s.answers; answer++) {
    const Row row = Send::form(S, o, seed, answer);
    std::printf("FORM answer=%u name=%s kind=%u target=", answer, row.name.c_str(), (unsigned)row.kind);
    pv(row.target);
    std::printf("\n");
    std::printf("MAIN");
    for (u64 j = 0; j < (u64(1) << c.main_bits); j++) {
      std::printf(" ");
      pv(row.coefficient(o, Part::MAIN, j));
    }
    std::printf("\nMASK");
    for (u64 j = 0; j < (u64(1) << c.mask_bits); j++) {
      std::printf(" ");
      pv(row.coefficient(o, Part::MASK, j));
    }
    std::printf("\n");
  }
  return 0;
}
