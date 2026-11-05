// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for the verifier-reachable public data of WF (`blocks/iop/wf.h`): the derived sizes and
// lookups, the layout, the plane callback, the row weights and a pending row. The prover's heavy
// part (`WfHeavy`, `WfCpu`) is not used. Build with -DBLK_FIELD=2.

#include "iop/wf.h"

#include <cstdio>
#include <memory>
#include <utility>
#include <vector>

using namespace blk;

namespace {

void pf(F x) { std::printf("%016llx", (unsigned long long)x.v); }
void pe(const E &x) {
  pf(x.c[0]);
  std::printf(",");
  pf(x.c[1]);
  std::printf(",");
  pf(x.c[2]);
}
void pes(const std::vector<E> &v) {
  if (v.empty()) {
    std::printf("-");
    return;
  }
  for (size_t i = 0; i < v.size(); i++) {
    if (i) std::printf(";");
    pe(v[i]);
  }
}
void punsigned(const std::vector<unsigned> &v) {
  if (v.empty()) {
    std::printf("-");
    return;
  }
  for (size_t i = 0; i < v.size(); i++) std::printf(i ? ",%u" : "%u", v[i]);
}

WfRun run(u64 first_place, u64 first_row, u64 places, u64 stride) {
  WfRun r;
  r.first_place = first_place;
  r.first_row = first_row;
  r.places = places;
  r.stride = stride;
  return r;
}
WfPart part(unsigned log_places, std::vector<WfRun> runs) {
  WfPart p;
  p.log_places = log_places;
  p.runs = std::move(runs);
  return p;
}
WfLookup lookup(const char *name, unsigned d, unsigned mu, unsigned live, std::vector<F> weights, F offset, F padding_key,
                std::vector<WfPart> parts, std::vector<unsigned> first_bound) {
  WfLookup l;
  l.name = name;
  l.d = d;
  l.mu = mu;
  l.live = live;
  l.digit_weight = std::move(weights);
  l.offset = offset;
  l.padding_key = padding_key;
  l.parts = std::move(parts);
  l.first_bound = std::move(first_bound);
  return l;
}
OracleShape shape(const char *name, CodeId code, size_t main_rows, size_t mask_rows, CodeId mask_code, unsigned answers) {
  OracleShape s;
  s.name = name;
  s.code = code;
  s.main_rows = main_rows;
  s.main_deg = 1;
  s.mask_rows = mask_rows;
  s.mask_code = mask_code;
  s.answers = answers;
  return s;
}
E at(u64 base, u64 i) { return E{{F{base + i}, F{base + i + 1}, F{base + i + 2}}}; }

void print_tensor(const char *tag, size_t i, const Tensor &t) {
  std::printf("%s tensor=%zu scalar=", tag, i);
  pe(t.scalar);
  std::printf(" vars=%u dense=%d dvars=", t.vars(), (int)t.has_dense());
  if (t.dense_vars.empty()) {
    std::printf("-");
  } else {
    for (size_t d = 0; d < t.dense_vars.size(); d++) std::printf(d ? ",%u" : "%u", t.dense_vars[d]);
  }
  std::printf(" first=%llu", (unsigned long long)t.first);
  if (t.values) {
    std::printf(" len=%zu", t.values->size());
  } else {
    std::printf(" len=-");
  }
  std::printf("\n");
}

// Codes of the minimal, valid case.
Codes minimal_codes() {
  Codes codes;
  codes.base.push_back(Code{7, 4, 2});    // log_n, ell, r
  codes.mask.push_back(Code{5, 32, 0});
  codes.mask.push_back(Code{7, 128, 0});
  return codes;
}
// The matrix of the minimal case: two rows, two columns.
WfMatrix minimal_matrix() { return WfMatrix{1, 2}; }
// A lookup whose keys cover both rows; its planes split into two blocks.
WfLookup minimal_lookup() {
  return lookup("bytes", 1, 2, 3, {F{1}}, F{0}, F{0}, {part(1, {run(0, 0, 2, 0)})}, {});
}
WfPublic minimal_public() {
  WfPublic x;
  x.lookups.push_back(minimal_lookup());
  x.message.shape = shape("ranges-msg", 0, 2, 2, 0, 1);
  x.message.leaf_class = 7;
  x.message_id = 1;
  x.stages.push_back(IoppStage{0, 0, 1, 1});
  x.stages.push_back(IoppStage{0, 1, 0, 0});
  x.choice.masks_ride = false;
  return x;
}

// The richer case, for the derived data that need not pass wf_fault.
WfPublic rich_public() {
  WfPublic x;
  x.lookups.push_back(lookup("lo", 2, 2, 0, {F{1}}, F{5}, F{3},
                             {part(2, {run(0, 0, 3, 0)}), part(1, {run(0, 3, 1, 0)})}, {0}));
  x.lookups.push_back(lookup("li", 3, 2, 0, {F{2}, F{3}}, F{1}, F{2}, {part(1, {run(0, 2, 1, 1)})}, {0}));
  x.lookups.push_back(lookup("lz", 2, 2, 3, {F{4}}, F{0}, F{1}, {part(1, {run(0, 0, 2, 0)})}, {}));
  x.message.shape = shape("ranges-msg", 0, 2, 2, 0, 2);
  x.message.leaf_class = 7;
  x.message_id = 3;
  x.stages.push_back(IoppStage{0, 0, 1, 1});
  x.stages.push_back(IoppStage{0, 1, 0, 0});
  x.choice.masks_ride = true;
  return x;
}
Codes rich_codes() {
  Codes codes;
  codes.base.push_back(Code{5, 32, 1});
  codes.mask.push_back(Code{5, 32, 0});
  return codes;
}
WfMatrix rich_matrix() { return WfMatrix{2, 8}; }

void dump_lookups(const WfPublic &x, const WfMatrix &m) {
  const std::vector<LkpPublic> all = wf_lookups(x, m);
  std::printf("LOOKUPS n=%zu\n", all.size());
  for (size_t i = 0; i < all.size(); i++) {
    const LkpPublic &p = all[i];
    std::printf("LKP i=%zu parts=", i);
    punsigned(p.parts);
    std::printf(" d=%u mu=%u live=%u h=%u g=%u shifted=%d read_from=", p.d, p.mu, p.live, p.h, p.g, (int)p.shifted);
    if (p.read_from.empty()) {
      std::printf("-");
    } else {
      for (size_t j = 0; j < p.read_from.size(); j++) std::printf(j ? ",%u" : "%u", p.read_from[j]);
    }
    std::printf(" keys=");
    if (p.keys.empty()) {
      std::printf("-");
    } else {
      for (size_t j = 0; j < p.keys.size(); j++)
        std::printf(j ? "|%llu:%u:%d:%llu" : "%llu:%u:%d:%llu", (unsigned long long)p.keys[j].first,
                    p.keys[j].log_trees, p.keys[j].function, (unsigned long long)p.keys[j].padding_row);
    }
    std::printf(" tables=");
    if (p.tables.empty()) {
      std::printf("-");
    } else {
      for (size_t j = 0; j < p.tables.size(); j++)
        std::printf(j ? "|%llu:%u:%u:%zu" : "%llu:%u:%u:%zu", (unsigned long long)p.tables[j].first,
                    p.tables[j].log_rows, p.tables[j].function, p.tables[j].rows.size());
    }
    std::printf(" padding=");
    if (p.padding.empty()) {
      std::printf("-");
    } else {
      for (size_t j = 0; j < p.padding.size(); j++)
        std::printf(j ? "|%u:%llu:%u:%llu:%llu" : "%u:%llu:%u:%llu:%llu", p.padding[j].part,
                    (unsigned long long)p.padding[j].first, p.padding[j].log_step,
                    (unsigned long long)p.padding[j].length, (unsigned long long)p.padding[j].row);
    }
    std::printf(" order=");
    punsigned(p.last_key_level_order);
    std::printf("\n");
  }
}

void dump_layout(const WfPublic &x, u64 ell) {
  const std::vector<WfBlock> blocks = wf_layout(x, ell);
  std::printf("LAYOUT ell=%llu n=%zu\n", (unsigned long long)ell, blocks.size());
  for (size_t i = 0; i < blocks.size(); i++)
    std::printf("BLOCK i=%zu lookup=%zu first=%u log=%u bits=%u row=%llu at=%llu\n", i, blocks[i].lookup,
                blocks[i].planes.first, blocks[i].planes.second, blocks[i].bits,
                (unsigned long long)blocks[i].row, (unsigned long long)blocks[i].first_place);
}

void dump_planes(const WfPublic &x, const Codes &codes) {
  for (size_t i = 0; i < x.lookups.size(); i++) {
    const unsigned mu = x.lookups[i].mu, d = x.lookups[i].d;
    const unsigned row_bits = ceil_log2(x.message.shape.main_rows);
    const unsigned log_ell = codes.base[x.message.shape.code].log_ell();
    std::vector<E> z;
    for (unsigned t = 0; t < mu + d; t++) z.push_back(at(100 + 10 * i, t));
    Tensor v = Tensor::eq(z.data(), (unsigned)z.size());
    Row row;
    LkpPlanesAt planes = wf_planes_at(x, codes, i);
    planes(row, std::move(v));
    std::printf("PLANES i=%zu vars=%u log_ell=%u row_bits=%u n=%llu\n", i, (unsigned)z.size(), log_ell, row_bits,
                (unsigned long long)(u64(1) << (log_ell + row_bits)));
    std::printf("PLZ i=%zu ", i);
    pes(z);
    std::printf("\n");
    for (u64 j = 0; j < (u64(1) << (log_ell + row_bits)); j++) {
      std::printf("PLANE i=%zu j=%llu v=", i, (unsigned long long)j);
      pe(row.coefficient(x.message_id, Part::MAIN, j));
      std::printf("\n");
    }
  }
}

void dump_weights_case(const char *name, unsigned k_row, u64 first_row, size_t len, u64 first, u64 count) {
  std::vector<E> values;
  for (size_t i = 0; i < len; i++) values.push_back(E{{F{1000 + i}, F{2000 + i}, F{3000 + i}}});
  std::shared_ptr<const std::vector<E>> shared = std::make_shared<std::vector<E>>(values);
  std::vector<Tensor> g;
  wf_weights_on_rows(k_row, first_row, shared, first, count, E{{F{7}, F{8}, F{9}}}, g);
  std::printf("WEIGHTS case=%s k_row=%u first_row=%llu first=%llu count=%llu values=%zu n=%zu\n", name, k_row,
              (unsigned long long)first_row, (unsigned long long)first, (unsigned long long)count, values.size(),
              g.size());
  for (size_t i = 0; i < g.size(); i++) {
    print_tensor("WT", i, g[i]);
    for (u64 j = 0; j < (u64(1) << k_row); j++) {
      std::printf("WV case=%s tensor=%zu j=%llu v=", name, i, (unsigned long long)j);
      pe(g[i].at(j));
      std::printf("\n");
    }
  }
}

void dump_pending() {
  const WfMatrix m = rich_matrix();
  const WfPublic x = rich_public();
  const WfLookup &l = x.lookups[0];
  const WfPart &p = l.parts[0];
  std::vector<E> point;
  point.push_back(E{{F{11}, F{12}, F{13}}});
  point.push_back(E{{F{21}, F{22}, F{23}}});
  point.push_back(E{{F{31}, F{32}, F{33}}});
  point.push_back(E{{F{41}, F{42}, F{43}}});
  // The covered places, as wf_pending_row computes them, so that an entry Form can sum to them.
  std::vector<E> e{E::one()};
  for (unsigned t = 0; t < p.log_places; t++) {
    const E z = point[m.k_col + t];
    const size_t half = e.size();
    e.resize(2 * half);
    for (size_t i = 0; i < half; i++) e[half + i] = e[i] * z, e[i] = e[i] - e[half + i];
  }
  E covered = E::zero();
  for (const WfRun &r : p.runs)
    for (u64 i = 0; i < r.places; i++) covered += e[r.first_place + i];
  LkpKeys claim;
  claim.point = point;
  claim.weights.entries.push_back({0, covered});
  claim.target = E{{F{71}, F{72}, F{73}}};
  const E target = claim.target;
  TensorRow row = wf_pending_row(m, l, p, std::move(claim));
  std::printf("PENDING k_row=%u n=%llu tensors=%zu\n", m.k_row(), (unsigned long long)(u64(1) << m.k_row()),
              row.g.size());
  std::printf("PCOVERED ");
  pe(covered);
  std::printf("\nPPOINT ");
  pes(point);
  std::printf("\nPTARGET ");
  pe(target);
  std::printf("\nPPSI ");
  pes(row.psi);
  std::printf("\nPROWTARGET ");
  pe(row.target);
  std::printf("\nPMASKS %zu\n", row.masks.size());
  for (size_t i = 0; i < row.g.size(); i++) {
    print_tensor("PT", i, row.g[i]);
    for (u64 j = 0; j < (u64(1) << m.k_row()); j++) {
      std::printf("PV tensor=%zu j=%llu v=", i, (unsigned long long)j);
      pe(row.g[i].at(j));
      std::printf("\n");
    }
  }
}

void dump_faults() {
  const Codes codes = minimal_codes();
  const WfMatrix m = minimal_matrix();
  const WfPublic x = minimal_public();
  auto show = [](const char *name, const char *f) { std::printf("FAULT name=%s value=%s\n", name, f ? f : "none"); };

  show("run_no_places", public_fault(run(0, 0, 0, 0)));
  show("part_too_many_places", public_fault(WfPart{41, {run(0, 0, 1, 0)}}));
  show("part_overlap", public_fault(part(2, {run(0, 0, 2, 0), run(1, 0, 2, 0)})));
  show("part_beyond", public_fault(part(2, {run(3, 0, 2, 0)})));
  show("part_empty", public_fault(WfPart{1, {}}));

  WfPart good_part = part(1, {run(0, 0, 2, 0)});
  WfLookup bad = lookup("bad", 1, 0, 0, {F{1}}, F{0}, F{0}, {good_part}, {});
  show("lookup_planes", public_fault(bad));
  bad = lookup("bad", 1, 2, 0, {}, F{0}, F{0}, {good_part}, {});
  show("lookup_no_digit", public_fault(bad));
  bad = lookup("bad", 1, 2, 0, {F{0}}, F{0}, F{0}, {good_part}, {});
  show("lookup_zero_weight", public_fault(bad));
  bad = lookup("bad", 2, 2, 0, {F{1}}, F{0}, F{4}, {good_part}, {});
  show("lookup_padding", public_fault(bad));
  bad = lookup("bad", 1, 2, 0, {F{1}}, F{0}, F{0}, {good_part}, {0, 0});
  show("lookup_bound_twice", public_fault(bad));
  bad = lookup("bad", 1, 2, 0, {F{1}}, F{0}, F{0}, {part(1, {run(0, 0, 2, 1)})}, {});
  show("lookup_stride_one_digit", public_fault(bad));
  bad = lookup("bad", 1, 2, 0, {F{1}, F{2}}, F{0}, F{0}, {part(1, {run(0, 0, 2, 0)})}, {});
  show("lookup_no_stride", public_fault(bad));

  WfPublic empty = x;
  empty.lookups.clear();
  show("public_no_lookup", public_fault(empty));
  WfPublic no_main = x;
  no_main.message.shape.main_rows = 0;
  show("public_no_main", public_fault(no_main));

  show("wf_ok", wf_fault(codes, x, m));
  show("wf_no_rows", wf_fault(codes, x, WfMatrix{1, 0}));
  show("wf_run_beyond", wf_fault(codes, x, WfMatrix{1, 1}));
  show("wf_part_keys", wf_fault(codes, x, WfMatrix{2, 2}));
  show("wf_uncovered", wf_fault(codes, x, WfMatrix{1, 3}));

  WfPublic variant = x;
  variant.message.shape.code = 5;
  show("wf_bad_code", wf_fault(codes, variant, m));
  variant = x;
  variant.message.shape.code = 1;  // a code shorter than the block of planes
  Codes short_code = codes;
  short_code.base.push_back(Code{6, 2, 0});
  show("wf_block_long", wf_fault(short_code, variant, m));
  variant = x;
  variant.message.shape.main_rows = 1;
  show("wf_main_rows", wf_fault(codes, variant, m));
  variant = x;
  variant.message.shape.mask_code = 2;
  Codes small_mask = codes;
  small_mask.mask.push_back(Code{5, 8, 0});
  show("wf_mask_room", wf_fault(small_mask, variant, m));
  variant = x;
  variant.stages[0].code = 1;
  show("wf_stage_code", wf_fault(codes, variant, m));
  variant = x;
  variant.stages[0].k = 0;
  variant.stages[0].h = 0;
  show("wf_iopp", wf_fault(codes, variant, m));
}

} // namespace

int main() {
  const WfPublic rich = rich_public();
  const WfMatrix rich_m = rich_matrix();
  const Codes rich_c = rich_codes();

  // The public bytes of the rich case.
  {
    Writer w;
    public_bytes(w, rich);
    std::printf("PUBLIC_BYTES ");
    for (u8 b : w.bytes()) std::printf("%02x", b);
    std::printf("\n");
  }

  dump_lookups(rich, rich_m);
  std::printf("SIZES index_masks=%zu index_mask_entries=%zu own_masks=%zu rows_batched=%llu\n",
              wf_index_masks(rich, rich_m), wf_index_mask_entries(rich, rich_m), wf_own_masks(rich, rich_m),
              (unsigned long long)wf_rows_batched(rich, rich_m));

  dump_layout(rich, 32);
  dump_layout(rich, 16);

  // Coverage: the rich case covers none; the minimal case's one lookup covers every row.
  std::printf("COVERS rows=%llu", (unsigned long long)rich_m.rows);
  for (size_t i = 0; i < rich.lookups.size(); i++) std::printf(" i%zu=%d", i, (int)wf_covers_all_rows(rich, i, rich_m));
  std::printf("\n");
  std::printf("COVERS rows=%llu i0=%d\n", (unsigned long long)minimal_matrix().rows,
              (int)wf_covers_all_rows(minimal_public(), 0, minimal_matrix()));

  dump_planes(rich, rich_c);
  dump_weights_case("A", 4, 5, 10, 1, 5);
  dump_weights_case("B", 4, 0, 16, 0, 16);
  dump_weights_case("C", 0, 0, 1, 0, 1);
  dump_pending();

  // WF's first fold and its prover message's notices.
  {
    const FoldShape F = wf_first_fold(rich);
    std::printf("FOLD code=%u mask_code=%u k=%u h=%u leaf=%u keep=%d alone=%d rounds=%d\n", F.code, F.mask_code,
                F.layout.k, F.layout.h, F.mask_leaf_class, (int)F.keep_folded_coefficients,
                (int)F.folded_coefficients_alone, (int)F.target_from_the_rounds);
    const std::vector<OracleNotice> msg = wf_message(rich);
    std::printf("MESSAGE n=%zu\n", msg.size());
    for (size_t i = 0; i < msg.size(); i++) {
      std::string name = msg[i].shape.name;
      for (char &c : name)
        if (c == ' ') c = '_';
      std::printf("NOTICE i=%zu name=%s code=%u main=%zu deg=%u mask=%zu mask_code=%u answers=%u leaf=%u\n", i,
                  name.c_str(), msg[i].shape.code, msg[i].shape.main_rows, msg[i].shape.main_deg,
                  msg[i].shape.mask_rows, msg[i].shape.mask_code, msg[i].shape.answers, msg[i].leaf_class);
    }
  }

  dump_faults();
  return 0;
}
