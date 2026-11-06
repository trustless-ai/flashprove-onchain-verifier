// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for LINK's public shape, messages, key faults, column lists and equality row
// (blocks/iop/link.h), and for member.h's claims, stretched weights and row checks.
// Build with -DBLK_FIELD=2.
//
// The protocol makes a `SampleReceipt` only through SEND's pass-key. This tool sends no oracle
// message, so, like blocks/iop/tests/toy_support.h does for tests without one, it opens the one
// constructor that it needs. The macro below lets `iop/mask.h` be included with its private parts
// public; every header that mask.h pulls in is included first, so the macro reaches only mask.h.

#include "base.h"

#include <cstdio>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#define private public
#include "iop/mask.h"
#undef private

#include "iop/link.h"
#include "iop/member.h"

using namespace blk;

namespace {

E e(u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; }

void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}

void pvec(const std::vector<E> &v) {
  for (size_t i = 0; i < v.size(); i++) {
    if (i) std::printf(";");
    pv(v[i]);
  }
}

void pdense(const Tensor &t) {
  if (t.dense_vars.empty()) {
    std::printf("none");
    return;
  }
  for (size_t i = 0; i < t.dense_vars.size(); i++) std::printf(i ? ",%u" : "%u", t.dense_vars[i]);
}

// One tensor in a form the Rust test can rebuild: its count of variables, its dense variables, its
// scalar, and every entry.
void ptensor(const char *kind, size_t i, const Tensor &t) {
  std::printf("T kind=%s i=%llu vars=%u dense=", kind, (unsigned long long)i, t.vars());
  pdense(t);
  std::printf(" scalar=");
  pv(t.scalar);
  std::printf(" at=");
  const u64 n = u64(1) << t.vars();
  for (u64 j = 0; j < n; j++) {
    if (j) std::printf(";");
    pv(t.at(j));
  }
  std::printf("\n");
}

void pshape(const char *prefix, const OracleShape &s) {
  std::printf("%s name=%s code=%u main_rows=%llu main_deg=%u mask_rows=%llu mask_code=%u answers=%u\n", prefix,
              s.name.c_str(), (unsigned)s.code, (unsigned long long)s.main_rows, s.main_deg,
              (unsigned long long)s.mask_rows, (unsigned)s.mask_code, s.answers);
}

void pnote(const OracleNotice &n) {
  std::printf("NOTICE name=%s code=%u main_rows=%llu main_deg=%u mask_rows=%llu mask_code=%u answers=%u leaf=%u\n",
              n.shape.name.c_str(), (unsigned)n.shape.code, (unsigned long long)n.shape.main_rows, n.shape.main_deg,
              (unsigned long long)n.shape.mask_rows, (unsigned)n.shape.mask_code, n.shape.answers, n.leaf_class);
}

const char *fault_or_none(const char *f) { return f ? f : "none"; }

Digest digest_with(u64 x) {
  Digest d{};
  for (int i = 0; i < 8; i++) d.w[i] = (u32)(x + (u64)i);
  return d;
}

// The codes of the vector: one base code for the folded rows (and the group's main rows), one mask
// code for the group's first stage, and a wider one for the test's last stage, whose mask row must
// hold the previous stage's two mask rows, its tail and its sample.
Codes link_codes() {
  Codes c;
  c.base.push_back(Code{6, 8, 1});
  c.mask.push_back(Code{6, 8, 1});
  c.mask.push_back(Code{6, 32, 1});
  return c;
}

// The committed table both sides link: 4 rows, one answer each, a row of 8 entries of which 3 are
// the answer's pad.
IndexShape link_table() {
  IndexShape t;
  t.code = Code{5, 8, 2};
  t.v = 2;
  t.answers = 1;
  t.salt_bytes = 40;
  t.distances = TableDistances{1, 2, 3, 4};
  return t;
}

// The LINK shape the vectors use. The test is a group of two-stage IOPP: stage 0 is the two folded
// rows' group (k = 1 + ceil_log2(4) = 3, h = 0); stage 1 is the last, with one main row and its own
// wider mask code.
LinkShape link_shape(const Codes &) {
  LinkShape S;
  S.table = link_table();
  S.columns_first = 2;
  S.columns_further = 3;
  S.code = 0;
  S.mask_code = 0;
  S.rows = 4;
  S.rows_high = false;
  S.leaf_class = 1;
  S.masks_ahead = true;
  S.later.push_back(IoppStage{0, 1, 0, 0});
  S.choice.masks_ride = true;
  return S;
}

}  // namespace

int main() {
  const Codes codes = link_codes();
  const LinkShape S = link_shape(codes);
  const unsigned samples = 2;

  std::printf("LABEL link=%llx\n", (unsigned long long)LINK_LABEL);
  std::printf("SHAPE v=%u entry_bits=%u cut=%llu rows=%llu columns_first=%llu columns_further=%llu code=%u mask_code=%u rows_high=%d leaf_class=%u masks_ahead=%d later=",
              S.v(), S.entry_bits(), (unsigned long long)S.cut(), (unsigned long long)S.rows,
              (unsigned long long)S.columns_first, (unsigned long long)S.columns_further, (unsigned)S.code,
              (unsigned)S.mask_code, (int)S.rows_high, S.leaf_class, (int)S.masks_ahead);
  const std::vector<IoppStage> test = S.test();
  for (size_t i = 0; i < test.size(); i++)
    std::printf("%s%u:%u:%u:%u", i ? ";" : "", (unsigned)test[i].code, (unsigned)test[i].mask_code, test[i].k,
                test[i].h);
  std::printf("\n");

  {
    const FoldeqShape f = S.first(samples), g = S.further(samples);
    std::printf("SIDE first columns=%llu entries=%llu tail_first=%llu\n", (unsigned long long)f.columns,
                (unsigned long long)f.entries(), (unsigned long long)f.tail_first());
    pshape("SIDE_U", f.u);
    std::printf("SIDE further columns=%llu entries=%llu tail_first=%llu\n", (unsigned long long)g.columns,
                (unsigned long long)g.entries(), (unsigned long long)g.tail_first());
    pshape("SIDE_U", g.u);
  }

  // The faults, by one changed field at a time (the first that a checker meets is the one shown).
  std::printf("FAULT name=valid public=%s link=%s\n", fault_or_none(public_fault(S)),
              fault_or_none(link_fault(codes, S, samples)));
  {
    LinkShape x = S;
    x.columns_first = 0;
    std::printf("FAULT name=no_column public=%s link=%s\n", fault_or_none(public_fault(x)),
                fault_or_none(link_fault(codes, x, samples)));
  }
  {
    LinkShape x = S;
    x.rows = 0;
    std::printf("FAULT name=no_rows public=%s link=%s\n", fault_or_none(public_fault(x)),
                fault_or_none(link_fault(codes, x, samples)));
  }
  {
    LinkShape x = S;
    x.later.clear();
    std::printf("FAULT name=one_stage public=%s link=%s\n", fault_or_none(public_fault(x)),
                fault_or_none(link_fault(codes, x, samples)));
  }
  {
    LinkShape x = S;
    x.table.answers = 0;
    std::printf("FAULT name=no_answers public=%s link=%s\n", fault_or_none(public_fault(x)),
                fault_or_none(link_fault(codes, x, samples)));
  }
  {
    LinkShape x = S;
    x.mask_code = 2;
    std::printf("FAULT name=no_mask_code public=%s link=%s\n", fault_or_none(public_fault(x)),
                fault_or_none(link_fault(codes, x, samples)));
  }
  {
    LinkShape x = S;
    x.code = 3;
    std::printf("FAULT name=no_code public=%s link=%s\n", fault_or_none(public_fault(x)),
                fault_or_none(link_fault(codes, x, samples)));
  }
  {
    LinkShape x = S;
    x.later[0].k = 1;
    std::printf("FAULT name=last_stage_rows public=%s link=%s\n", fault_or_none(public_fault(x)),
                fault_or_none(link_fault(codes, x, samples)));
  }
  {
    Codes c = codes;
    c.mask[0].ell = 4;
    std::printf("FAULT name=mask_too_short public=%s link=%s\n", fault_or_none(public_fault(S)),
                fault_or_none(link_fault(c, S, samples)));
  }

  // The oracle messages of LINK's first prover message, and the fold shape of the mask sent ahead.
  {
    const std::vector<OracleNotice> m = link_message(S, samples);
    std::printf("MESSAGE masks_ahead=%d count=%llu\n", (int)S.masks_ahead, (unsigned long long)m.size());
    for (const OracleNotice &n : m) pnote(n);
    const FoldShape F = link_fold_shape(S);
    std::printf("FOLD code=%u mask_code=%u k=%u h=%u members=%llu mask_leaf=%u keep=%d alone=%d target=%d\n",
                (unsigned)F.code, (unsigned)F.mask_code, F.layout.k, F.layout.h,
                (unsigned long long)F.layout.members.size(), F.mask_leaf_class, (int)F.keep_folded_coefficients,
                (int)F.folded_coefficients_alone, (int)F.target_from_the_rounds);
    LinkShape q = S;
    q.masks_ahead = false;
    std::printf("MESSAGE_NO_MASK count=%llu\n", (unsigned long long)link_message(q, samples).size());
  }

  // link_key_fault on hand-built keys: honest, another shape, another configuration, a short record
  // and a table whose numbers are no code.
  {
    const Digest configuration = digest_with(7);
    const Digest root = digest_with(11);
    IndexRecord rec;
    rec.y.assign(S.table.rows() * S.table.answers, e(600));
    const IndexKey good(S.table, configuration, root, rec);
    std::printf("KEY name=good fault=%s link=%s\n", fault_or_none(good.fault()),
                fault_or_none(link_key_fault(configuration, S.table, good)));
    {
      IndexShape t = S.table;
      t.v = 3;
      IndexRecord r;
      r.y.assign(t.rows() * t.answers, e(601));
      const IndexKey key(t, configuration, root, r);
      std::printf("KEY name=other_shape fault=%s link=%s\n", fault_or_none(key.fault()),
                  fault_or_none(link_key_fault(configuration, S.table, key)));
    }
    {
      const IndexKey key(S.table, digest_with(8), root, rec);
      std::printf("KEY name=other_configuration fault=%s link=%s\n", fault_or_none(key.fault()),
                  fault_or_none(link_key_fault(configuration, S.table, key)));
    }
    {
      IndexRecord r = rec;
      r.y.pop_back();
      const IndexKey key(S.table, configuration, root, r);
      std::printf("KEY name=short_record fault=%s link=%s\n", fault_or_none(key.fault()),
                  fault_or_none(link_key_fault(configuration, S.table, key)));
    }
    {
      IndexShape t = S.table;
      t.answers = 0;
      IndexRecord r;
      const IndexKey key(t, configuration, root, r);
      std::printf("KEY name=no_answers fault=%s link=%s\n", fault_or_none(key.fault()),
                  fault_or_none(link_key_fault(configuration, S.table, key)));
    }
  }

  // The one list of positions, split into the two tables' columns.
  {
    const PositionList drawn = PositionList::from_draws({17, 3, 9, 3, 21}, S.table.code.log_n);
    const LinkLists l = link_lists(S, drawn);
    std::printf("LISTS log_n=%u draws=%llu\n", drawn.log_n(), (unsigned long long)drawn.draws().size());
    for (int side = 0; side < 2; side++) {
      const PositionList &p = side ? l.further : l.first;
      std::printf("LIST side=%d log_n=%u size=%llu draws=", side, p.log_n(), (unsigned long long)p.draws().size());
      for (size_t i = 0; i < p.draws().size(); i++) std::printf(i ? ",%llu" : "%llu", (unsigned long long)p.draws()[i]);
      std::printf(" all=");
      for (size_t i = 0; i < p.all().size(); i++) std::printf(i ? ",%llu" : "%llu", (unsigned long long)p.all()[i]);
      std::printf("\n");
    }
  }

  // The equality claim: eq(phi, .) before the cut, on the first folded row, minus on the further.
  {
    const VectorLay lay = vector_lay(codes, S.first(samples).u, S.rows_high);
    FoldedRow first;
    first.oracle = 0;
    first.lay = lay;
    FoldedRow further;
    further.oracle = 1;
    further.lay = lay;
    std::vector<E> phi(S.entry_bits());
    for (size_t i = 0; i < phi.size(); i++) phi[i] = e(500 + i);
    const Row row = link_equality_row(S, phi, first, further, S.cut());
    std::printf("EQ name=%s target=", row.name.c_str());
    pv(row.target);
    std::printf(" terms=%llu units=%llu runs=%llu forms=%llu phi=", (unsigned long long)row.terms.size(),
                (unsigned long long)row.units.size(), (unsigned long long)row.runs.size(),
                (unsigned long long)row.forms.size());
    pvec(phi);
    std::printf(" lay_row_bits=%u lay_place_bits=%u lay_rows_high=%d\n", lay.row_bits, lay.place_bits,
                (int)lay.rows_high);
    for (int side = 0; side < 2; side++) {
      const OracleId o = side ? 1 : 0;
      for (u64 j = 0; j < (u64(1) << lay.bits()); j++) {
        std::printf("EQVAL side=%d j=%llu coeff=", side, (unsigned long long)j);
        pv(row.coefficient(o, Part::MAIN, j));
        std::printf("\n");
      }
    }
  }

  // A shared vector of row weights and the tensors that stretch_in_the_cube makes of it.
  {
    const unsigned k_row = 3;
    auto values = std::make_shared<const std::vector<E>>(std::vector<E>{e(11), e(12), e(13)});
    const std::vector<Tensor> g = member_inner::stretch_in_the_cube(k_row, 3, values);
    std::printf("STRETCH k_row=%u first_row=3 values=", k_row);
    pvec(*values);
    std::printf(" tensors=%llu\n", (unsigned long long)g.size());
    for (size_t i = 0; i < g.size(); i++) ptensor("stretch", i, g[i]);
  }

  // member_weights_on_rows: the same through LinShape, ending exactly at the matrix's last row.
  {
    LinShape L;
    L.matrix_rows = 8;
    L.k_lo = 1;
    L.fold.index.v = 2;  // k_col = 3
    auto values = std::make_shared<const std::vector<E>>(std::vector<E>{e(21), e(22), e(23), e(24), e(25)});
    const std::vector<Tensor> g = member_weights_on_rows(L, 2, values);
    std::printf("WEIGHTS matrix_rows=%llu k_row=%u k_col=%u first_row=2 values=",
                (unsigned long long)L.matrix_rows, L.k_row(), L.k_col());
    pvec(*values);
    std::printf(" tensors=%llu\n", (unsigned long long)g.size());
    for (size_t i = 0; i < g.size(); i++) ptensor("weights", i, g[i]);
  }

  // The pending claim that a sub-proof leaves, and LIN's form of it. The mask entries come from a
  // receipt for oracle message 0, whose free entries begin at index 0.
  {
    SampleReceipt receipt(0, 0, 4);
    MaskLedger ledger(std::move(receipt));

    const std::vector<E> phi2{e(2), e(3)};
    auto values = std::make_shared<const std::vector<E>>(std::vector<E>{e(201), e(202)});
    Tensor dense;
    dense.push_dense(1);
    dense.insert_choice(1, 1, 1);
    dense.set_values(values, 0);
    const std::vector<E> psi{e(301), e(302), e(303)};
    const E target = e(400);

    std::printf("ROW target=");
    pv(target);
    std::printf(" psi=");
    pvec(psi);
    std::printf(" masks=2\n");
    ptensor("row", 0, Tensor::eq(phi2.data(), 2));
    ptensor("row", 1, dense);

    // member_pending_row moves in one mask entry: index 0, coefficient beta.
    MaskSlot slot = ledger.take();
    const E beta = e(31);
    std::vector<Tensor> pending_g;
    pending_g.push_back(Tensor::eq(phi2.data(), 2));
    pending_g.push_back(dense);
    TensorRow pending = member_pending_row(std::move(pending_g), psi, std::move(slot), beta, target);
    std::printf("PENDING target=");
    pv(pending.target);
    std::printf(" psi=");
    pvec(pending.psi);
    std::printf(" masks=%llu\n", (unsigned long long)pending.masks.size());
    for (size_t i = 0; i < pending.masks.size(); i++) {
      // part is always MASK for a member's pending row; it is printed for the Rust parser.
      std::printf("PENDING_MASK i=%llu oracle=%u part=%u index=%u coeff=", (unsigned long long)i,
                  pending.masks[i].slot.oracle(), (unsigned)Part::MASK, pending.masks[i].slot.index());
      pv(pending.masks[i].coeff);
      std::printf("\n");
    }
    for (size_t i = 0; i < pending.g.size(); i++) ptensor("pending", i, pending.g[i]);

    // member_claim: the same claim with its mask entries consumed into LIN's form.
    TensorRow row;
    row.target = target;
    row.psi = psi;
    row.g.push_back(Tensor::eq(phi2.data(), 2));
    row.g.push_back(dense);
    row.masks.push_back({ledger.take(), e(21)});
    row.masks.push_back({ledger.take(), e(22)});
    const LinClaim claim = member_claim(std::move(row));
    std::printf("CLAIM target=");
    pv(claim.target);
    std::printf(" psi=");
    pvec(claim.psi);
    std::printf(" g=%llu masks=%llu\n", (unsigned long long)claim.g.size(),
                (unsigned long long)claim.masks.size());
    for (size_t i = 0; i < claim.g.size(); i++) ptensor("claim", i, claim.g[i]);
    for (size_t i = 0; i < claim.masks.size(); i++) {
      std::printf("CLAIM_MASK i=%llu oracle=%u part=%u index=%llu coeff=", (unsigned long long)i,
                  claim.masks[i].oracle, (unsigned)claim.masks[i].part, (unsigned long long)claim.masks[i].index);
      pv(claim.masks[i].coeff);
      std::printf("\n");
    }
  }

  // member_rows_fit on a small statement: the index-mask message is oracle 0 of the statement, a
  // sampled message of mask rows alone; two pending rows name its entries.
  {
    Statement st(codes);
    OracleShape masks;
    masks.name = "index masks";
    masks.main_rows = 0;
    masks.mask_rows = 2;
    masks.mask_code = 0;
    masks.answers = 1;
    const OracleId index_masks = st.sent(masks);

    LinShape L;
    L.matrix_rows = 3;
    L.k_lo = 1;
    L.fold.index.v = 2;  // k_col = 3
    L.own_mask_code = 0;

    SampleReceipt receipt(index_masks, 0, 8);
    MaskLedger ledger(std::move(receipt));
    const std::vector<E> phi2{e(2), e(3)};
    std::vector<TensorRow> pending;
    for (size_t r = 0; r < 2; r++) {
      TensorRow t;
      t.target = e(700 + r);
      t.psi = {e(701), e(702), e(703)};
      t.g.push_back(Tensor::eq(phi2.data(), 2));
      t.masks.push_back({ledger.take(), e(710 + r)});
      pending.push_back(std::move(t));
    }
    member_rows_fit(st, L, index_masks, pending);
    std::printf("ROWS_FIT index_masks=%u rows=%llu k_col=%u k_row=%u ok=1\n", index_masks,
                (unsigned long long)pending.size(), L.k_col(), L.k_row());
  }
  return 0;
}
