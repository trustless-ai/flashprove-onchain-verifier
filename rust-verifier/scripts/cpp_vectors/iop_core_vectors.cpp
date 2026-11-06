// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for the instantiable cores of blocks/iop/: mask ledgers, the statement and a group's
// layout, BAT's combine, laid matrices/tensors/forms, single_rows_symbols, and BATT's claim/row.
// Build with -DBLK_FIELD=2.

#include "code/code.h"
#include "iop/bat.h"
#include "iop/batt.h"
#include "iop/laid.h"
#include "iop/mask.h"
#include "iop/relation.h"
#include "iop/single_rows.h"

#include <cstdio>
#include <utility>
#include <vector>

using namespace blk;

// The pass-key that tests define (blocks/iop/tests/toy_support.h:31-33); send.h is not included.
namespace blk {
struct SendAccess {
  static SampleReceipt make(u32 oracle, u32 first, u32 count, u32 rows, unsigned log_rows) {
    return SampleReceipt(oracle, first, count, rows, log_rows);
  }
};
} // namespace blk

namespace {
E e(u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; }
void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
template <class T> void plist(const char *name, const std::vector<T> &v) {
  std::printf("%s=", name);
  if (v.empty()) std::printf("-");
  for (size_t i = 0; i < v.size(); i++) {
    if (i) std::printf(";");
    pv(v[i]);
  }
}
void pidx(const char *name, const std::vector<u64> &v) {
  std::printf("%s=", name);
  if (v.empty()) std::printf("-");
  for (size_t i = 0; i < v.size(); i++) std::printf("%s%llu", i ? ";" : "", (unsigned long long)v[i]);
}
void plist_bool(const char *name, const std::vector<bool> &v) {
  std::printf("%s=", name);
  if (v.empty()) std::printf("-");
  for (size_t i = 0; i < v.size(); i++) std::printf("%s%d", i ? ";" : "", (int)v[i]);
}
void row_at(const char *name, const Row &r, unsigned bits) {
  std::printf("%s ", name);
  plist("terms_ok", std::vector<E>());
  std::printf("target=");
  pv(r.target);
  std::printf(" units=%zu runs=%zu forms=%zu terms=%zu\n", r.units.size(), r.runs.size(), r.forms.size(), r.terms.size());
  (void)bits;
}
} // namespace

int main() {
  // Mask ledgers: the skipped row numbers and the order of the entries.
  {
    MaskLedger l(SendAccess::make(4, 0, 7, 3, 2));
    std::vector<u64> got;
    while (l.left() > 0) got.push_back(l.take().index());
    std::printf("LEDGER oracle=4 rows=3 log_rows=2 ");
    pidx("taken", got);
    std::printf(" left=%u\n", l.left());
    l.close();
    std::printf("LEDGER_CLOSED left=%u\n", l.left());
  }

  Codes codes;
  codes.base.push_back(Code{3, 4, 2});
  codes.mask.push_back(Code{2, 4, 2});
  Statement S(codes);

  OracleShape sa;
  sa.name = "A", sa.code = 0, sa.main_rows = 2, sa.main_deg = 1, sa.mask_rows = 2, sa.mask_code = 0, sa.answers = 1;
  OracleShape sb;
  sb.name = "B", sb.code = 0, sb.main_rows = 1, sb.main_deg = 3, sb.mask_rows = 1, sb.mask_code = 0, sb.answers = 0;
  const OracleId oa = S.sent(sa), ob = S.sent(sb);
  {
    std::vector<Row> samples(1);
    samples[0].name = "sample of A";
    samples[0].target = e(900);
    S.sampled(SendAccess(), oa, std::move(samples), {}, SendAccess::make(oa, 0, 4, 2, 1));
  }
  const GroupId g = S.new_group("G", 0, 0);
  S.join(g, oa);

  Row r1;
  r1.name = "r1";
  r1.add(oa, Part::MAIN, Tensor::eq(std::vector<E>{e(1), e(2), e(3)}.data(), 3));
  r1.add_unit(oa, Part::MAIN, 5, e(11));
  r1.add_run(oa, Part::MAIN, 1, 2, std::vector<E>{e(12), e(13)});
  r1.target = e(99);
  Row r2;
  r2.name = "r2";
  r2.add_unit(oa, Part::MASK, 0, e(7));
  r2.target = e(100);
  S.add_row(g, std::move(r1));
  S.add_row(g, std::move(r2));

  const GroupLayout L0 = S.layout(g);
  std::printf("LAYOUT k=%u h=%u log_ell=%u log_ell_zk=%u ", L0.k, L0.h, L0.log_ell, L0.log_ell_zk);
  pidx("members", std::vector<u64>(L0.members.begin(), L0.members.end()));
  std::printf(" ");
  plist_bool("kept", L0.kept);
  std::printf(" ");
  pidx("main_first", L0.main_first);
  std::printf(" ");
  pidx("mask_first", L0.mask_first);
  std::printf("\n");

  RunInput in = S.begin_run(g);
  const GroupLayout &L = in.layout;
  const GroupRow out = Bat::combine(S, g, std::move(in), e(123));
  std::printf("BAT k=%u h=%u target=", L.k, L.h);
  pv(out.target);
  std::printf(" d_size=%zu kept=%zu\n", out.d.size(), out.kept.size());
  const unsigned vars = L.k + codes.base[0].log_ell();
  std::printf("BAT_FORM vars=%u ", vars);
  std::vector<E> cf;
  for (u64 j = 0; j < (u64(1) << vars); j++) cf.push_back(out.c.at(j));
  plist("c", cf);
  std::printf(" target=");
  pv(out.target);
  std::printf("\n");
  std::printf("BAT_D ");
  plist("d", out.d);
  std::printf("\n");

  // A laid block, a laid matrix, and the tensor/form it makes.
  {
    LaidBlock b;
    b.first_i = 0, b.first_c = 0, b.first_row = 0, b.first_place = 0;
    b.bits_i = 2, b.bits_c = 2, b.row_bits = 2, b.place_bits = 2, b.i_is_low = true;
    std::printf("LAID_BLOCK ok=%d %s\n", (int)laid_block_ok(b, 2, 2), public_fault(b) ? public_fault(b) : "-");
    LaidMatrix m;
    m.size_i = 4, m.size_c = 4, m.blocks = {b};
    std::printf("LAID_MATRIX ok=%d\n", (int)laid_ok(std::vector<LaidMatrix>{m}, 2, 2));
    IndexWeights on_i = IndexWeights::eq({e(1), e(2)});
    IndexWeights on_c = IndexWeights::powers(e(3), 2);
    Tensor t = laid_tensor(b, 2, 2, on_i, on_c, e(5));
    std::printf("LAID_TENSOR vars=%u scalar=", t.vars());
    pv(t.scalar);
    std::vector<E> at;
    for (u64 j = 0; j < 16; j++) at.push_back(t.at(j));
    plist(" at", at);
    std::printf("\n");
    Form f = laid_form({b}, 2, 2, on_i, on_c, e(5));
    std::vector<E> fa;
    for (u64 j = 0; j < 16; j++) fa.push_back(f.at(j));
    std::printf("LAID_FORM vars=%u ", 4);
    plist("f", fa);
    std::printf("\n");
  }

  // SingleRows symbols at two opened positions.
  {
    SingleRows s;
    s.code = 0, s.mask_code = 0, s.layout = L0, s.gamma = {e(1)}, s.masks = 2, s.fresh = 1;
    s.kept_rows = 0;
    Opened opened;
    opened.of.assign(2, std::vector<Opened::Column>(2));
    for (size_t i = 0; i < 2; i++) {
      opened.of[0][i].main = {e(10 + i), e(20 + i)};
      opened.of[0][i].mask = {e(30 + i), e(40 + i)};
      opened.of[1][i].mask = {e(70 + i), e(80 + i)};
    }
    std::vector<E> y = single_rows_symbols(s, opened, 2);
    std::printf("SYMBOLS rows=%zu ", s.rows());
    plist("y", y);
    std::printf("\n");
  }

  // BATT: the claim from two tensor rows and the row that comes out.
  {
    MaskLedger ledger(SendAccess::make(5, 0, 20, 4, 2));
    std::vector<TensorRow> rows(2);
    std::vector<F> f = {F{2}, F{3}, F{4}};
    rows[0].g = {Tensor::product(f.data(), 3, e(7))};
    rows[0].psi = {e(1), e(2)};
    rows[0].masks.push_back(MaskTerm<E>{ledger.take(), e(3)});
    rows[0].target = e(31);
    rows[1].g = {Tensor::product(f.data(), 3, e(8))};
    rows[1].psi = {e(4), e(5)};
    rows[1].masks.push_back(MaskTerm<E>{ledger.take(), e(6)});
    rows[1].target = e(32);
    BattClaim b = batt_claim(rows, e(33));
    std::printf("BATT k_col=%u ", batt_k_col(rows));
    plist("chi", b.chi);
    std::printf(" target=");
    pv(b.claim.target);
    std::printf(" masks=%zu vars=%zu shown=%u kept=%u degree=%u\n", b.claim.masks.size(), b.claim.vars.size(),
                b.summand.shown, b.summand.kept, b.summand.degree);
    std::vector<E> at_point = {e(40), e(41)};
    std::vector<E> no_y;
    std::vector<E> a = b.summand.at(at_point, no_y);
    plist("BATT_AT a", a);
    std::printf("\n");
    PscOutput<E> out;
    out.point = {e(50), e(51)};
    out.row_maps.push_back(KeptTerm<E>{0, e(9)});
    out.row_masks.push_back(MaskTerm<E>{ledger.take(), e(10)});
    out.row_target = e(52);
    TensorRow r = batt_row(rows, std::move(out));
    std::printf("BATT_ROW g=%zu scalar=", r.g.size());
    pv(r.g[0].scalar);
    std::printf(" ");
    plist("psi", r.psi);
    std::printf(" target=");
    pv(r.target);
    std::printf(" masks=%zu\n", r.masks.size());
  }

  // PSC's output rows, from what both sides know at the end.
  {
    MaskLedger pl(SendAccess::make(6, 0, 50, 1, 0));
    SumClaim<E> claim;
    claim.vars = {Weight<E>::plain(3), Weight<E>::equality(e(60), 3)};
    claim.target = e(61);
    claim.masks.push_back(MaskTerm<E>{pl.take(), e(62)});
    Summand<E> sm;
    sm.shown = 1, sm.kept = 1, sm.degree = 1;
    const E a0 = e(63), a1 = e(64), a2 = e(65);
    sm.at = [a0, a1, a2](const std::vector<E> &point, const std::vector<E> &) {
      return std::vector<E>{a0 + point[0], a1};
    };
    const std::vector<Weight<E>> vars = psc_vars(claim, sm);
    std::vector<MaskSlot> fresh = pl.take(psc_masks(claim, sm));
    std::vector<E> challenges = {e(70), e(71), e(72)};
    std::vector<E> end_values = {e(73)};
    PscOutput<E> out = psc_rows(std::move(claim), sm, vars, std::move(fresh), e(74), challenges, e(75), end_values);
    plist("PSC_POINT", out.point);
    std::printf(" masks=%zu keeps=%zu target=", out.row_masks.size(), out.row_maps.size());
    pv(out.row_target);
    std::printf("\n");
    std::vector<E> mc;
    for (const MaskTerm<E> &m : out.row_masks) mc.push_back(m.coeff);
    plist("PSC_MASKS", mc);
    std::printf("\n");
    std::printf("PSC_KEEPS n=%zu", out.row_maps.size());
    for (const KeptTerm<E> &t : out.row_maps) {
      std::printf(" map=%u coeff=", t.map);
      pv(t.coeff);
    }
    std::printf(" ends=%zu\n", out.ends.size());
    std::printf("PSC_END ");
    plist("point", out.ends[0].point);
    std::printf(" value=");
    pv(out.ends[0].value);
    std::printf(" masks=%zu", out.ends[0].masks.size());
    std::printf("\n");
  }

  (void)oa, (void)ob, (void)row_at;
  return 0;
}
