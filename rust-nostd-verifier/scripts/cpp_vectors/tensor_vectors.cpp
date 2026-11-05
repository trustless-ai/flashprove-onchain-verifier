// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for blocks/iop/tensor.h: Tensor product forms, choices, dense slices, folding,
// evaluation and Form sums, frozen parts and entry merging. Build with
// clang++ -O2 -std=c++17 -Iblocks -DBLK_FIELD=2.

#include "iop/tensor.h"

#include <cstdio>
#include <vector>

using namespace blk;

namespace {
E ev(u64 s, unsigned i) { return E{{F{s * 101 + i * 3 + 1}, F{s * 211 + i * 5 + 2}, F{s * 307 + i * 7 + 3}}}; }
F fv(u64 s, unsigned i) { return F{s * 401 + i * 11 + 1}; }
void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
void pvs(const std::vector<E> &v) {
  if (v.empty()) std::printf("-");
  for (size_t i = 0; i < v.size(); i++) {
    if (i) std::printf(";");
    pv(v[i]);
  }
}
void tensor(const char *id, const Tensor &t) {
  std::printf("T id=%s vars=%u scalar=", id, t.vars());
  pv(t.scalar);
  std::printf(" pick_mask=%016llx pick_value=%016llx pairs=", (unsigned long long)t.pick_mask(),
              (unsigned long long)t.pick_value());
  std::vector<E> p;
  for (unsigned i = 0; i < t.vars(); i++)
    if (!t.picks(i)) p.push_back(t.lo(i)), p.push_back(t.hi(i));
  pvs(p);
  std::printf(" dense=");
  if (t.dense_vars.empty()) std::printf("-");
  for (size_t i = 0; i < t.dense_vars.size(); i++) std::printf("%s%u", i ? "," : "", t.dense_vars[i]);
  std::printf(" first=%llu values=%zu\n", (unsigned long long)t.first, t.values ? t.values->size() : 0);
}
void ats(const char *op, const char *id, const Tensor &t, unsigned n) {
  for (unsigned j = 0; j < n; j++) {
    std::printf("%s id=%s j=%u v=", op, id, j);
    pv(t.at(j));
    std::printf("\n");
  }
}
void addout(const char *id, const Tensor &t, unsigned n) {
  std::vector<E> out(n, E::zero());
  t.add_to(out.data());
  std::printf("ADD id=%s out=", id);
  pvs(out);
  std::printf("\n");
}
void form(const char *id, const Form &f) {
  std::printf("FORM id=%s ntensors=%zu nentries=%zu nfrozen=%zu empty=%d\n", id, f.tensors.size(), f.entries.size(),
              f.frozen.size(), (int)f.empty());
}
void fats(const char *op, const char *id, const Form &f, unsigned n) {
  for (unsigned j = 0; j < n; j++) {
    std::printf("%s id=%s j=%u v=", op, id, j);
    pv(f.at(j));
    std::printf("\n");
  }
}
void faddout(const char *id, const Form &f, unsigned vars) {
  std::vector<E> out(size_t(1) << vars, E::zero());
  f.add_to(out.data(), vars);
  std::printf("FADD id=%s out=", id);
  pvs(out);
  std::printf("\n");
}
void fixed(const char *id, Tensor t, const std::vector<E> &g, unsigned count) {
  t.fix_low(g.data(), count);
  tensor(id, t);
}
} // namespace

int main() {
  // 0: eq
  {
    std::vector<E> z = {ev(1, 0), ev(1, 1), ev(1, 2)};
    Tensor t = Tensor::eq(z.data(), 3, ev(2, 0));
    tensor("T0", t);
    std::printf("MLE id=T0 v=");
    pv(t.mle(z.data()));
    std::printf("\n");
    std::printf("PART id=T0 from=0 count=2 v=");
    pvs(t.part(0, 2));
    std::printf("\n");
    std::printf("PART id=T0 from=1 count=2 v=");
    pvs(t.part(1, 2));
    std::printf("\n");
    ats("AT", "T0", t, 8);
    addout("T0", t, 8);
    std::vector<E> g = {ev(3, 0), ev(3, 1), ev(3, 2)};
    fixed("T0F", t, g, 1);
    fixed("T0F2", t, g, 2);
  }

  // 1: product
  {
    std::vector<F> f = {fv(4, 0), fv(4, 1), fv(4, 2)};
    Tensor t = Tensor::product(f.data(), 3, ev(2, 1));
    tensor("T1", t);
    std::printf("MLE id=T1 v=");
    std::vector<E> x = {ev(5, 0), ev(5, 1), ev(5, 2)};
    pv(t.mle(x.data()));
    std::printf("\n");
    ats("AT", "T1", t, 8);
    addout("T1", t, 8);
  }

  // 2: pushes, choices, set_pair, rotate, insert_choice
  {
    Tensor t;
    t.scalar = ev(6, 0);
    t.push(ev(6, 1), ev(6, 2));
    t.push(E::zero(), E::one());
    t.push(E::one(), E::zero());
    tensor("T2", t);
    t.set_pair(0, ev(6, 3), ev(6, 4));
    tensor("T2S", t);
    t.rotate(1);
    tensor("T2R", t);
    t.insert_choice(1, 2, 3);
    tensor("T2I", t);
    ats("AT", "T2I", t, 8);
    addout("T2I", t, 32);
    std::printf("PART id=T2I from=0 count=3 v=");
    pvs(t.part(0, 3));
    std::printf("\n");
  }

  // 3: dense variables, folding
  {
    Tensor t;
    t.scalar = ev(7, 0);
    t.push(ev(7, 1), ev(7, 2));
    t.push_dense(2);
    std::vector<E> values = {ev(8, 0), ev(8, 1), ev(8, 2), ev(8, 3)};
    t.set_values(std::make_shared<const std::vector<E>>(values), 0);
    tensor("T3", t);
    ats("AT", "T3", t, 8);
    std::vector<E> x = {ev(9, 0), ev(9, 1), ev(9, 2)};
    std::printf("MLE id=T3 v=");
    pv(t.mle(x.data()));
    std::printf("\n");
    std::vector<E> g = {ev(10, 0), ev(10, 1), ev(10, 2)};
    Tensor::Slice s = t.folded_slice(g.data(), 1);
    std::printf("FOLDED id=T3 count=1 values=");
    pvs(*s.values);
    std::printf(" factor=");
    pv(s.factor);
    std::printf("\n");
    fixed("T3F1", t, g, 1);
    Tensor t3f = t;
    t3f.fix_low(g.data(), 2);
    tensor("T3F2", t3f);
    addout("T3F2", t3f, 4);
    Tensor t2;
    t2.scalar = ev(11, 0);
    t2.push_dense(1);
    t2.push(ev(11, 1), ev(11, 2));
    std::vector<E> v2 = {ev(12, 0), ev(12, 1)};
    t2.set_values(std::make_shared<const std::vector<E>>(v2), 0);
    tensor("T3b", t2);
    fixed("T3bF", t2, g, 2);
  }

  // 4: Form sums, entries, scaling, fix_low, merging
  {
    std::vector<E> z = {ev(13, 0), ev(13, 1)};
    std::vector<F> pf = {fv(14, 0), fv(14, 1)};
    Form f;
    f.add(Tensor::eq(z.data(), 2, ev(15, 0)));
    f.add(Tensor::product(pf.data(), 2, ev(15, 1)));
    f.add_entry(0, ev(15, 2));
    f.add_entry(0, ev(15, 3));
    f.add_entry(3, ev(15, 4));
    form("F0", f);
    fats("FAT", "F0", f, 4);
    faddout("F0", f, 2);
    std::printf("MLE id=F0 v=");
    pv(f.mle(z.data(), 2));
    std::printf("\n");
    Form g;
    g.add_entry(1, ev(16, 0));
    g.scale(ev(16, 1));
    f.add(g, ev(16, 2));
    form("F1", f);
    fats("FAT", "F1", f, 4);
    faddout("F1", f, 2);
    std::vector<E> h = {ev(17, 0)};
    f.fix_low(h.data(), 1, ev(17, 1));
    form("F2", f);
    fats("FAT", "F2", f, 2);
    faddout("F2", f, 1);
  }

  // 5: frozen parts and their fast path
  {
    std::vector<E> z = {ev(18, 0), ev(18, 1)};
    Form f;
    f.add(Tensor::eq(z.data(), 2, ev(19, 0)));
    f.add_entry(2, ev(19, 1));
    f.freeze(2);
    form("F3", f);
    fats("FAT", "F3", f, 4);
    faddout("F3", f, 2);
    Form flat = f.flattened();
    form("F3L", flat);
    fats("FAT", "F3L", flat, 4);
    faddout("F3L", flat, 2);
    std::vector<E> g = {ev(20, 0), ev(20, 1)};
    f.fix_low(g.data(), 1, ev(20, 2));
    form("F4", f);
    fats("FAT", "F4", f, 2);
    faddout("F4", f, 1);

    Form h;
    h.add(Tensor::eq(z.data(), 2, ev(21, 0)));
    h.add_entry(2, ev(21, 1));
    h.freeze(2);
    h.insert_choice(0, 1, 0);
    form("F5", h);
    fats("FAT", "F5", h, 8);
    faddout("F5", h, 3);
    std::vector<E> g3 = {ev(22, 0), ev(22, 1), ev(22, 2)};
    h.fix_low(g3.data(), 1, ev(22, 3));
    form("F6", h);
    fats("FAT", "F6", h, 4);
    faddout("F6", h, 2);
  }
  return 0;
}
