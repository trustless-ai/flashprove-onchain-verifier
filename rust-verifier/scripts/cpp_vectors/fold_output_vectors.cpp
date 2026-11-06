// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for FOLD's output claim (fold.h:261-282). Build with
// `clang++ -O2 -std=c++17 -Iblocks -DBLK_FIELD=2`.

#include "code/code.h"
#include "iop/fold.h"

#include <cstdio>
#include <vector>

using namespace blk;

namespace {
E e(u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; }
void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
void plist(const char *name, const std::vector<E> &v) {
  std::printf("%s=", name);
  if (v.empty()) std::printf("-");
  for (size_t i = 0; i < v.size(); i++) {
    if (i) std::printf(";");
    pv(v[i]);
  }
}
} // namespace

int main() {
  Codes codes;
  codes.base.push_back(Code{3, 4, 2});
  codes.mask.push_back(Code{2, 4, 2});
  Statement st(codes);
  GroupLayout L;
  L.k = 1, L.h = 1, L.log_ell = 2, L.log_ell_zk = 2;
  GroupRow row;
  row.group = 0;
  const std::vector<F> f = {F{2}, F{3}, F{4}};
  row.c.add(Tensor::product(f.data(), 3, e(5)));
  for (u64 i = 0; i < 8; i++) row.d.push_back(e(300 + i));
  row.target = e(301);
  FoldShape S;
  S.code = 0, S.mask_code = 0, S.layout = L;
  FoldMask mask;
  mask.sent_as(1);
  std::vector<E> gamma = {e(80)};
  SingleRows rows = fold_output(st, S, std::move(row), 1, e(76), gamma, e(81));
  std::printf("FOLD_OUTPUT masks=%u d=%zu kept=%zu gamma=%zu target=", rows.masks, rows.d.size(), rows.kept.size(),
              rows.gamma.size());
  pv(rows.target);
  std::printf("\n");
  std::vector<E> c;
  for (u64 j = 0; j < 4; j++) c.push_back(rows.c.at(j));
  plist("FOLD_C", c);
  std::printf("\n");
  plist("FOLD_D0", rows.d[0]);
  std::printf("\n");
  plist("FOLD_D1", rows.d[1]);
  std::printf("\n");
  return 0;
}
