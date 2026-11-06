// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for the instantiable S2b-2 components: the mask ledger, the group layout and BAT's
// coefficient carry, BAT's row batching, BATT's claim and output row, and the matrix layout's
// tensors. The tool defines its own `SendAccess` as the C++ tests do (toy_support.h), because it
// includes no SEND block. Build with -DBLK_FIELD=2.

#include "code/code.h"
#include "iop/bat.h"
#include "iop/batt.h"
#include "iop/laid.h"
#include "iop/mask.h"
#include "iop/relation.h"
#include "iop/tensor.h"

#include <cstdio>
#include <vector>

using namespace blk;

namespace blk {
// The C++ tests' own pass-key (blocks/iop/tests/toy_support.h): no SEND block is included here.
struct SendAccess {
  static SampleReceipt make(u32 oracle, u32 first, u32 count, u32 rows, unsigned log_rows) {
    return SampleReceipt(oracle, first, count, rows, log_rows);
  }
};
} // namespace blk

namespace {
void pd(const char *name, const Digest &d) {
  std::printf("%s=", name);
  for (int i = 0; i < 8; i++) std::printf("%08x", d.w[i]);
}
void pf(const char *name, F x) {
  std::printf("%s=%016llx", name, (unsigned long long)x.v);
}
void pv(const char *name, const E &x) {
  std::printf("%s=%016llx,%016llx,%016llx", name, (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
E e_from(u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; }
Digest digest_from(u32 seed) {
  Digest d{};
  for (int i = 0; i < 8; i++) d.w[i] = seed * 0x9E3779B9u + (u32)i * 0x85EBCA6Bu;
  return d;
}
} // namespace

int main() {
  // ---- the mask ledger ----
  {
    MaskLedger ledger(SendAccess::make(3, 1, 12, 3, 2));
    std::printf("LEDGER oracle=3 first=1 count=12 rows=3 log_rows=2\n");
    for (int j = 0; j < 12; j++) {
      MaskSlot s = ledger.take();
      std::printf("TAKE j=%d oracle=%u index=%u left=%u\n", j, s.oracle(), s.index(), ledger.left());
    }
    ledger.close();
    std::printf("CLOSED left=%u\n", ledger.left());
  }

  // ---- the group layout ----
  {
    Codes codes;
    codes.base.push_back(Code{3, 2, 1});
    codes.mask.push_back(Code{2, 2, 1});
    Statement S(codes);
    auto sampled = [&](OracleShape shape) {
      const OracleId o = S.sent(shape);
      S.sampled(SendAccess(), o, {Row()}, {}, SendAccess::make(o, 0, 4, 1, 0));
      return o;
    };
    OracleShape a;
    a.name = "a", a.code = 0, a.main_rows = 2, a.main_deg = 1, a.mask_rows = 2, a.mask_code = 0, a.answers = 1;
    OracleShape b = a;
    b.name = "b", b.main_rows = 4;
    OracleShape c = a;
    c.name = "c", c.main_rows = 1;
    const OracleId oa = sampled(a), ob = sampled(b), oc = sampled(c);
    const GroupId g = S.new_group("g", 0, 0);
    S.join(g, oa);
    S.join(g, ob);
    S.join(g, oc, true);
    const GroupLayout L = S.layout(g);
    std::printf("LAYOUT members=%u,%u,%u kept=%d,%d,%d k=%u h=%u log_ell=%u log_ell_zk=%u\n", oa, ob, oc,
                (int)L.kept[0], (int)L.kept[1], (int)L.kept[2], L.k, L.h, L.log_ell, L.log_ell_zk);
    std::printf("MAIN_FIRST");
    for (u64 x : L.main_first) std::printf(" %llu", (unsigned long long)x);
    std::printf("\nMASK_FIRST");
    for (u64 x : L.mask_first) std::printf(" %llu", (unsigned long long)x);
    std::printf("\n");
    std::printf("GROUP_INDEX");
    for (u64 idx : {(u64)0, (u64)1, (u64)2, (u64)3}) std::printf(" %llu", (unsigned long long)group_index(idx, 1, 0, 2));
    std::printf("\n");

    // BAT's carry: one open claim with a term, a unit, a run and a form.
    Row row;
    row.name = "carry";
    row.add(oa, Part::MAIN, Tensor::product(std::vector<F>{F{3}, F{5}}.data(), 2, e_from(7)));
    row.add_unit(oa, Part::MAIN, 1, e_from(11));
    row.add_run(oa, Part::MASK, 0, 2, std::vector<E>{e_from(13), e_from(17)});
    Form f;
    f.add_entry(2, e_from(19));
    row.add_form(oa, f);
    row.target = e_from(23);
    S.add_row(g, std::move(row));
    RunInput in = S.begin_run(g);
    GroupRow out = Bat::combine(S, g, std::move(in), e_from(29));
    std::printf("BAT_CARRY target=");
    pv("v", out.target);
    std::printf(" d=");
    for (size_t j = 0; j < out.d.size(); j++) {
      if (j) std::printf(";");
      pv("", out.d[j]);
    }
    std::printf(" kept=%zu c=", out.kept.size());
    for (u64 j = 0; j < (u64(1) << (L.k + L.log_ell)); j++) {
      if (j) std::printf(",");
      std::printf("%016llx", (unsigned long long)out.c.at(j).c[0].v);
    }
    std::printf("\n");
  }

  // ---- BAT's pure row batching ----
  {
    Row a, b;
    a.name = "a";
    a.add_unit(0, Part::MAIN, 2, e_from(31));
    a.target = e_from(37);
    b.name = "b";
    b.add_unit(1, Part::MASK, 0, e_from(41));
    b.add_run(1, Part::MASK, 1, 1, std::vector<E>{e_from(43), e_from(47)});
    b.target = e_from(53);
    Row out = Bat::combine({a, b}, e_from(59), "batched");
    std::printf("BAT_ROWS target=");
    pv("v", out.target);
    std::printf(" units=%zu runs=%zu\n", out.units.size(), out.runs.size());
    for (u64 j = 0; j < 4; j++) {
      std::printf("BAT_AT j=%llu ", (unsigned long long)j);
      pv("v", out.coefficient(0, Part::MAIN, j));
      std::printf("\n");
    }
  }

  // ---- BATT's claim and output row ----
  {
    std::vector<TensorRow> rows;
    for (int j = 0; j < 2; j++) {
      TensorRow r;
      r.g.push_back(Tensor::product(std::vector<F>{F{80 + (u64)j}, F{90 + (u64)j}}.data(), 2, e_from(100 + j)));
      r.psi = {e_from(110 + j), e_from(120 + j)};
      r.target = e_from(130 + j);
      rows.push_back(std::move(r));
    }
    BattClaim b = batt_claim(rows, e_from(7));
    std::printf("BATT chi=");
    for (size_t j = 0; j < b.chi.size(); j++) {
      if (j) std::printf(";");
      pv("", b.chi[j]);
    }
    std::printf(" target=");
    pv("v", b.claim.target);
    std::vector<E> gamma{e_from(140), e_from(150)};
    std::vector<E> a = b.summand.at(gamma, {});
    std::printf(" AT");
    for (size_t j = 0; j < a.size(); j++) {
      std::printf(" ");
      pv("", a[j]);
    }
    std::printf("\n");
    PscOutput<E> out;
    out.point = gamma;
    out.row_maps.push_back(KeptTerm<E>{0, e_from(160)});
    out.row_target = e_from(170);
    TensorRow r = batt_row(rows, std::move(out));
    std::printf("BATT_ROW target=");
    pv("v", r.target);
    std::printf(" psi=");
    for (size_t j = 0; j < r.psi.size(); j++) {
      if (j) std::printf(";");
      pv("", r.psi[j]);
    }
    std::printf(" g=%zu\n", r.g.size());
    for (u64 j = 0; j < 8; j++) {
      std::printf("BATT_G i=%llu ", (unsigned long long)j);
      pv("v", r.g[0].at(j));
      std::printf("\n");
    }
  }

  // ---- the matrix layout's tensors ----
  {
    const unsigned row_bits = 2, place_bits = 2;
    LaidMatrix m;
    m.size_i = 2, m.size_c = 2;
    m.blocks.push_back(LaidBlock{0, 0, 0, 0, 1, 1, 1, 1, true});
    std::printf("LAID ok=%d fault=%d\n", (int)laid_ok({m}, row_bits, place_bits),
                (int)(public_fault(m.blocks[0]) != nullptr));
    IndexWeights on_i = IndexWeights::eq({e_from(200)});
    IndexWeights on_c = IndexWeights::eq({e_from(210)});
    Form f = laid_form(m.blocks, row_bits, place_bits, on_i, on_c, e_from(220));
    std::printf("LAID_FORM n=%zu", f.tensors.size());
    for (u64 j = 0; j < (u64(1) << (row_bits + place_bits)); j++) {
      if (j % 4 == 0) std::printf(" |");
      std::printf(" %016llx", (unsigned long long)f.at(j).c[0].v);
    }
    std::printf("\n");
    LaidBlock bad{1, 0, 0, 0, 1, 1, 1, 1, true};
    std::printf("LAID_BAD fault=%d in_table=%d\n", (int)(public_fault(bad) != nullptr),
                (int)laid_block_ok(bad, row_bits, place_bits));
  }

  // ---- send pads and ledger sizes ----
  {
    Codes codes;
    codes.base.push_back(Code{4, 4, 2});
    codes.mask.push_back(Code{3, 4, 2});
    OracleShape s;
    s.name = "pad";
    s.code = 0;
    s.main_rows = 2;
    s.main_deg = 1;
    s.mask_rows = 2;
    s.mask_code = 0;
    s.answers = 2;
    // The same rule as Send::pad (send.h:163-178), written here because send.h is not included.
    const unsigned row_bits = ceil_log2(s.mask_rows);
    const size_t len = codes.mask[s.mask_code].ell;
    std::printf("PAD");
    for (unsigned i = 0; i < s.answers; i++) {
      for (unsigned t = 0; t < 1; t++) {
        const u64 place = len - s.answers + i + t;
        const u64 index = (s.mask_rows - 1) + (place << row_bits);
        std::printf(" %llu", (unsigned long long)index);
      }
    }
    std::printf("\n");
  }
  return 0;
}
