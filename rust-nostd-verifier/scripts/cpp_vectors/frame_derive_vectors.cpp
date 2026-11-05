// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for `derive()` (`blocks/frame/derive.h:125-149`) with the default `FrameShape`, from the
// accepted parameter file. Prints every derived size, so the Rust test replays it.
//
// Usage: frame_derive_vectors <policy.txt>

#include <cstdio>
#include <fstream>
#include <string>

#include "frame/derive.h"

using namespace blk;

static std::string hex(const std::string &s) {
  static const char *d = "0123456789abcdef";
  std::string o;
  for (unsigned char c : s) o += d[c >> 4], o += d[c & 15];
  return o;
}

static std::string group_str(const GroupSize &g) {
  char b[512];
  std::snprintf(b, sizeof b,
                "name=%s main=%u,%llu,%llu,%d mask=%u,%llu,%llu,%d k=%u h=%u slots=%llu "
                "rule=%u m=%llu",
                hex(g.name).c_str(), g.main.log_n, (unsigned long long)g.main.ell,
                (unsigned long long)g.main.r, g.main.over_E ? 1 : 0, g.mask.log_n,
                (unsigned long long)g.mask.ell, (unsigned long long)g.mask.r, g.mask.over_E ? 1 : 0,
                g.k, g.h, (unsigned long long)g.slots, (unsigned)g.rule,
                (unsigned long long)g.m);
  return b;
}

static void dump_test(const char *name, const TestSizes &x) {
  std::printf("TEST name=%s t=%llu group=%s stages=%zu\n", name, (unsigned long long)x.t,
              group_str(x.group).c_str(), x.stages.size());
  for (size_t i = 0; i < x.stages.size(); i++)
    std::printf("STAGE test=%s i=%zu t=%llu r_ood=%llu group=%s\n", name, i,
                (unsigned long long)x.stages[i].t, (unsigned long long)x.stages[i].r_ood,
                group_str(x.stages[i].g).c_str());
}

int main(int argc, char **argv) {
  if (argc != 2) {
    std::fprintf(stderr, "usage: frame_derive_vectors <policy.txt>\n");
    return 2;
  }
  std::ifstream f(argv[1], std::ios::binary);
  if (!f) {
    std::fprintf(stderr, "frame_derive_vectors: cannot read %s\n", argv[1]);
    return 2;
  }
  const std::string text((std::istreambuf_iterator<char>(f)), std::istreambuf_iterator<char>());
  Parameters p;
  std::string why;
  if (!read_parameters(text, p, why)) {
    std::printf("REFUSED why=%s\n", hex(why).c_str());
    return 0;
  }
  const FrameShape shape;
  const Derived d = derive(p, shape);
  std::printf("DERIVED refused=%s target=%u samples=%u salt=%u work=",
              d.refused.empty() ? "-" : hex(d.refused).c_str(), d.set.target, d.set.samples,
              d.set.salt_bytes);
  for (int i = 0; i < 6; i++)
    for (int j = 0; j < 3; j++) std::printf("%s%u", i || j ? "," : "", d.set.work[i][j]);
  std::printf("\n");
  dump_test("link", d.link);
  dump_test("last", d.last);
  std::printf("TABLE log_n=%u ell=%llu r=%llu v=%u answers=%u radius=%llu later=%llu m_once=%llu "
              "m_later=%llu\n",
              d.table.code.log_n, (unsigned long long)d.table.code.ell,
              (unsigned long long)d.table.code.r, d.table.v, d.table.answers,
              (unsigned long long)d.table.distances.radius,
              (unsigned long long)d.table.distances.later_radius,
              (unsigned long long)d.table.distances.m_once,
              (unsigned long long)d.table.distances.m_later);
  return 0;
}
