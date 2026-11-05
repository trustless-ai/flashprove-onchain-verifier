// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for the data and arithmetic of the S2b-2 blocks that are instantiable without a channel:
// mask.h (slots/ledger), laid.h (layouts and coefficient forms), bat.h (Bat::combine on a
// Statement), batt.h (BattClaim and batt_row), and psc.h (psc_vars/psc_masks/psc_rows). Build with
// -DBLK_FIELD=2.

#define BLK_PLANS_BY_HAND_FOR_A_TEST

#include "iop/bat.h"
#include "iop/batt.h"
#include "iop/laid.h"
#include "iop/psc.h"
#include "iop/relation.h"

#include <cstdio>
#include <memory>
#include <vector>

using namespace blk;

// The pass-key that mask.h makes only SEND able to create in a whole program. Here the tool stands
// in for SEND to build one receipt.
namespace blk {
struct SendAccess {
  static SampleReceipt receipt(u32 oracle, u32 first, u32 count, u32 rows, unsigned log_rows) {
    return SampleReceipt(oracle, first, count, rows, log_rows);
  }
};
} // namespace blk

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
void pfs(const std::vector<F> &v) {
  if (v.empty()) std::printf("-");
  for (size_t i = 0; i < v.size(); i++) std::printf("%s%016llx", i ? "," : "", (unsigned long long)v[i].v);
}
Codes codes() {
  Codes c;
  c.base.push_back(Code{4, 4, 2});
  c.mask.push_back(Code{2, 2, 1});
  return c;
}
Row plain_row() {
  Row r;
  r.name = "r";
  r.kind = RowKind::PLAIN;
  return r;
}
} // namespace

int main() {
  // ---- mask.h ----
  {
    SampleReceipt rec = SendAccess::receipt(3, 0, 9, 2, 2);
    MaskLedger l(std::move(rec));
    std::printf("MASK_START left=%u\n", l.left());
    for (int i = 0; i < 4; i++) {
      MaskSlot s = l.take();
      std::printf("SLOT i=%d oracle=%u index=%u left=%u\n", i, s.oracle(), s.index(), l.left());
    }
    l.close();
    std::printf("MASK_END left=%u\n", l.left());
  }

  // ---- laid.h ----
  {
    LaidBlock b;
    b.first_i = 0;
    b.first_c = 0;
    b.first_row = 0;
    b.first_place = 0;
    b.bits_i = 1;
    b.bits_c = 1;
    b.row_bits = 1;
    b.place_bits = 1;
    b.i_is_low = true;
    std::printf("LAID_BLOCK ok=%d fault=%s\n", (int)laid_block_ok(b, 2, 2), public_fault(b) ? public_fault(b) : "-");
    LaidBlock bad = b;
    bad.first_row = 1;
    std::printf("LAID_BAD ok=%d\n", (int)laid_block_ok(bad, 2, 2));
    LaidMatrix m;
    m.size_i = 2;
    m.size_c = 2;
    m.blocks.push_back(b);
    std::printf("LAID_OK ok=%d\n", (int)laid_ok({m}, 2, 2));
    IndexWeights on_i = IndexWeights::powers(ev(1, 0), 1);
    IndexWeights on_c = IndexWeights::powers(ev(1, 1), 1);
    Tensor t = laid_tensor(b, 2, 2, on_i, on_c, ev(1, 2));
    std::printf("LAID_T vars=%u at=", t.vars());
    for (u64 j = 0; j < 16; j++) {
      if (j) std::printf(";");
      pv(t.at(j));
    }
    std::printf(" pairs=");
    std::vector<E> pairs;
    for (unsigned i = 0; i < t.vars(); i++)
      if (!t.picks(i)) pairs.push_back(t.lo(i)), pairs.push_back(t.hi(i));
    pvs(pairs);
    std::printf("\n");
    std::vector<E> out(16, E::zero());
    t.add_to(out.data());
    std::printf("LAID_ADD out=");
    pvs(out);
    std::printf("\n");
    std::vector<E> written = {ev(2, 0), ev(2, 1), ev(2, 2), ev(2, 3)};
    auto values = std::make_shared<const std::vector<E>>(written);
    IndexWeights wi = IndexWeights::written(values);
    IndexWeights one = IndexWeights::powers(ev(3, 0), 1);
    Tensor w = laid_tensor(b, 2, 2, wi, one, ev(3, 1));
    std::printf("LAID_W vars=%u dense=%zu at=", w.vars(), w.dense_vars.size());
    for (u64 j = 0; j < 16; j++) {
      if (j) std::printf(";");
      pv(w.at(j));
    }
    std::printf("\n");
    Form f = laid_form({b}, 2, 2, on_i, on_c, ev(1, 2));
    std::vector<E> fout(16, E::zero());
    f.add_to(fout.data(), 4);
    std::printf("LAID_FORM ntensors=%zu out=", f.tensors.size());
    pvs(fout);
    std::printf("\n");
  }

  // ---- relation.h + Bat::combine ----
  {
    Codes c = codes();
    Statement S(c);
    OracleShape sh;
    sh.name = "oracle";
    sh.code = 0;
    sh.main_rows = 2;
    sh.main_deg = 1;
    sh.mask_rows = 2;
    sh.mask_code = 0;
    sh.answers = 1;
    const OracleId o = S.sent(sh);
    std::vector<Row> samples;
    Row srow = plain_row();
    srow.target = ev(4, 0);
    srow.add_unit(o, Part::MAIN, 0, ev(4, 1));
    samples.push_back(std::move(srow));
    S.sampled(SendAccess(), o, std::move(samples), {}, SendAccess::receipt(o, 0, 2, 2, 1));
    const GroupId g = S.new_group("g", 0, 0);
    S.join(g, o, false);
    const E z[3] = {ev(5, 0), ev(5, 1), ev(5, 4)};
    const F pf[3] = {fv(5, 2), fv(5, 3), fv(5, 5)};
    Row r = plain_row();
    r.add(o, Part::MAIN, Tensor::eq(z, 3, ev(6, 0)));
    r.add(o, Part::MAIN, Tensor::product(pf, 3, ev(6, 1)));
    r.add_unit(o, Part::MASK, 0, ev(6, 2));
    std::vector<E> run_own = {ev(6, 3), ev(6, 4)};
    r.add_run(o, Part::MAIN, 0, 1, run_own);
    r.target = ev(6, 5);
    S.add_row(g, std::move(r));
    Row r2 = plain_row();
    r2.add_unit(o, Part::MAIN, 1, ev(7, 0));
    r2.target = ev(7, 1);
    S.add_row(g, std::move(r2));
    RunInput in = S.begin_run(g);
    const unsigned k = in.layout.k;
    std::printf("BAT_LAYOUT k=%u h=%u members=%zu kept_rows=%zu\n", k, in.layout.h, in.layout.members.size(),
                in.layout.members.size());
    GroupRow gr = Bat::combine(S, g, std::move(in), ev(8, 0));
    std::printf("BAT_TARGET t=");
    pv(gr.target);
    std::printf(" group=%u d=", gr.group);
    pvs(gr.d);
    std::printf(" nkept=%zu\n", gr.kept.size());
    for (u64 j = 0; j < (u64(1) << (k + 2)); j++) {
      std::printf("BAT_AT j=%llu v=", (unsigned long long)j);
      pv(gr.c.at(j));
      std::printf("\n");
    }
    std::vector<E> out(size_t(1) << (k + 2), E::zero());
    gr.c.add_to(out.data(), k + 2);
    std::printf("BAT_ADD out=");
    pvs(out);
    std::printf("\n");
    Row lone = plain_row();
    lone.target = ev(9, 0);
    lone.add_unit(o, Part::MAIN, 1, ev(9, 2));
    Row combined = Bat::combine({lone}, ev(9, 1), "combined");
    std::printf("BAT_SIGMA target=");
    pv(combined.target);
    std::printf(" nterms=%zu nunits=%zu\n", combined.terms.size(), combined.units.size());
  }

  // ---- batt.h ----
  {
    std::vector<TensorRow> rows(2);
    const E z[2] = {ev(10, 0), ev(10, 1)};
    const F pf[2] = {fv(10, 2), fv(10, 3)};
    rows[0].g.push_back(Tensor::eq(z, 2, ev(11, 0)));
    rows[0].psi = {ev(11, 1), ev(11, 2)};
    rows[0].target = ev(11, 3);
    rows[1].g.push_back(Tensor::product(pf, 2, ev(11, 4)));
    rows[1].psi = {ev(11, 5), ev(11, 6)};
    rows[1].target = ev(11, 7);
    const unsigned k_col = batt_k_col(rows);
    std::printf("BATT_K k_col=%u masks=%zu\n", k_col, batt_masks(k_col));
    BattClaim bc = batt_claim(rows, ev(12, 0));
    std::printf("BATT_CLAIM chi=");
    pvs(bc.chi);
    std::printf(" target=");
    pv(bc.claim.target);
    std::printf(" vars=%zu kept=%u shown=%u degree=%u\n", bc.claim.vars.size(), bc.summand.kept, bc.summand.shown,
                bc.summand.degree);
    std::vector<E> point(k_col);
    for (unsigned j = 0; j < k_col; j++) point[j] = ev(12, j + 1);
    const std::vector<E> a = bc.summand.at(point, {});
    std::printf("BATT_S at=");
    pvs(a);
    std::printf("\n");
    PscOutput<E> out;
    out.point = point;
    SampleReceipt rec = SendAccess::receipt(0, 0, 8, 1, 0);
    MaskLedger l(std::move(rec));
    out.row_masks.push_back({l.take(), ev(13, 0)});
    out.row_maps.push_back({0, ev(13, 1)});
    out.row_target = ev(13, 2);
    TensorRow br = batt_row(rows, std::move(out));
    std::printf("BATT_ROW psi=");
    pvs(br.psi);
    std::printf(" target=");
    pv(br.target);
    std::printf(" ng=%zu masks=%zu\n", br.g.size(), br.masks.size());
    for (size_t i = 0; i < br.g.size(); i++) {
      std::printf("BATT_G i=%zu vars=%u at=", i, br.g[i].vars());
      for (u64 j = 0; j < (u64(1) << br.g[i].vars()); j++) {
        if (j) std::printf(";");
        pv(br.g[i].at(j));
      }
      std::printf("\n");
    }
  }

  // ---- psc.h rows ----
  {
    SumClaim<E> claim;
    claim.vars = {Weight<E>::plain(2), Weight<E>::equality(ev(14, 0), 2), Weight<E>::at_zero(3)};
    claim.target = ev(14, 1);
    SampleReceipt rec = SendAccess::receipt(1, 0, 32, 1, 0);
    MaskLedger l(std::move(rec));
    claim.masks.push_back({l.take(), ev(14, 2)});
    Summand<E> S;
    S.shown = 1;
    S.kept = 2;
    S.degree = 2;
    S.at = [](const std::vector<E> &point, const std::vector<E> &y) {
      std::vector<E> a{E::zero()};
      a[0] = point[0] + y[0];
      for (unsigned i = 0; i < 2; i++) a.push_back(point[(i + 1) % point.size()] + y[0]);
      return a;
    };
    const std::vector<Weight<E>> vars = psc_vars(claim, S);
    std::printf("PSC_SIZE masks=%zu vars=%zu\n", psc_masks(claim, S), vars.size());
    std::vector<MaskSlot> fresh = l.take(psc_masks(claim, S));
    std::vector<E> challenges = {ev(15, 0), ev(15, 1), ev(15, 2), ev(15, 3)};
    std::vector<E> ends = {ev(15, 4)};
    PscOutput<E> out = psc_rows(std::move(claim), S, vars, std::move(fresh), ev(15, 5), challenges, ev(15, 6), ends);
    std::printf("PSC_POINT ");
    pvs(out.point);
    std::printf("\nPSC_ROW_TARGET ");
    pv(out.row_target);
    std::printf("\nPSC_ROW_MASKS ");
    for (size_t i = 0; i < out.row_masks.size(); i++) {
      std::printf("%s%u,%u,", i ? ";" : "", out.row_masks[i].slot.oracle(), out.row_masks[i].slot.index());
      pv(out.row_masks[i].coeff);
    }
    std::printf("\nPSC_ROW_MAPS ");
    for (size_t i = 0; i < out.row_maps.size(); i++) {
      std::printf("%s%u,", i ? ";" : "", out.row_maps[i].map);
      pv(out.row_maps[i].coeff);
    }
    std::printf("\nPSC_ENDS n=%zu\n", out.ends.size());
    for (size_t i = 0; i < out.ends.size(); i++) {
      std::printf("PSC_END i=%zu value=", i);
      pv(out.ends[i].value);
      std::printf(" point=");
      pvs(out.ends[i].point);
      std::printf(" masks=");
      for (size_t j = 0; j < out.ends[i].masks.size(); j++) {
        std::printf("%s%u,%u,", j ? ";" : "", out.ends[i].masks[j].slot.oracle(), out.ends[i].masks[j].slot.index());
        pv(out.ends[i].masks[j].coeff);
      }
      std::printf("\n");
    }
  }
  return 0;
}
