// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for `tree_sizes` (`blocks/iop/context.h:150-165`). Each case dumps every tree's name,
// log_n, leaf bytes and one-list mark; the marks are numbered by a counter that runs across cases,
// as C++'s static counter does.
//
// Usage: frame_tree_sizes_vectors

#include <cstdio>
#include <string>
#include <vector>

#include "iop/context.h"

using namespace blk;

static Codes codes_of(unsigned log_n, unsigned log_n_zk) {
  Codes c;
  c.base.push_back(Code{log_n, 8, 4});
  c.mask.push_back(Code{log_n_zk, 4, 2});
  return c;
}

static OracleNotice notice(const char *name, unsigned code, unsigned mask_code, size_t main_rows,
                           size_t mask_rows, unsigned answers, unsigned leaf_class) {
  OracleNotice n;
  n.shape.name = name, n.shape.code = code, n.shape.mask_code = mask_code;
  n.shape.main_rows = main_rows, n.shape.main_deg = 1, n.shape.mask_rows = mask_rows;
  n.shape.answers = answers, n.leaf_class = leaf_class;
  return n;
}

static void dump(const char *name, const Codes &c, const std::vector<OracleNotice> &sent) {
  const std::vector<TreeSize> sizes = tree_sizes(c, sent);
  std::printf("TREES name=%s count=%zu\n", name, sizes.size());
  for (const TreeSize &t : sizes)
    std::printf("TREE name=%s log_n=%u leaf_bytes=%llu one_list=%d number=%llu where=%s\n", name,
                t.log_n, (unsigned long long)t.leaf_bytes, t.one_list ? 1 : 0,
                (unsigned long long)t.one_list.number, t.name.c_str());
}

int main() {
  const Codes c = codes_of(8, 6);
  dump("single", c, {notice("a", 0, 0, 64, 0, 1, 0)});
  dump("two_share", c, {notice("a", 0, 0, 64, 0, 1, 0), notice("b", 0, 0, 32, 0, 1, 0)});
  dump("two_classes", c, {notice("a", 0, 0, 64, 0, 1, 0), notice("b", 0, 0, 32, 0, 1, 1)});
  dump("mask_only", c, {notice("a", 0, 0, 0, 8, 1, 0)});
  dump("mixed", c, {notice("a", 0, 0, 64, 0, 1, 0), notice("b", 0, 0, 0, 8, 1, 0)});
  dump("one_list_first", c, {notice("a", 0, 0, 64, 0, 0, 0), notice("b", 0, 0, 32, 0, 1, 0)});
  dump("one_list_twice", c, {notice("a", 0, 0, 64, 0, 0, 0), notice("b", 0, 0, 32, 0, 0, 0)});
  dump("mask_one_list", c, {notice("a", 0, 0, 0, 8, 0, 0)});
  return 0;
}
