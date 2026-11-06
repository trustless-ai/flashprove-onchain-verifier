// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the frame's sizing and plan functions:
//   lin_sized(), lin_size_of(), lin_plan_first/shared/second() (blocks/frame/lin_frame.h),
//   link_sized(), link_plan() (blocks/frame/link_frame.h),
//   wf_sized(), wf_plan() (blocks/frame/wf_frame.h), and
//   req_plan() (blocks/iop/req.h:306-407).
// The sizes come from fixtures/config/policy.txt: read_parameters(), derive() with the default
// FrameShape, then lin_lines()/lin_sized() (normal and one-time), link_lines()/link_sized(), and
// wf_lines()/wf_sized() on a small explicit layout. The plans are dumped round by round, as
// plan_emitters_vectors.cpp dumps them. fp-host/tests/frame_sizes_vectors.rs replays every line.
//
// Usage: frame_sizes_vectors <policy.txt>

#include <cstdio>
#include <cstring>
#include <fstream>
#include <string>
#include <vector>

#include "frame/derive.h"
#include "frame/lin_frame.h"
#include "frame/link_frame.h"
#include "frame/wf_frame.h"
#include "frame/wf_units.h"
#include "iop/req.h"

using namespace blk;

namespace {

std::string hex(const std::string &s) {
  static const char *d = "0123456789abcdef";
  std::string o;
  o.reserve(2 * s.size());
  for (unsigned char c : s) o += d[c >> 4], o += d[c & 15];
  return o;
}

std::string hex_or_dash(const std::string &s) { return s.empty() ? "-" : hex(s); }

std::string group_str(const GroupSize &g) {
  char b[512];
  std::snprintf(b, sizeof b,
                "name=%s main=%u,%llu,%llu,%d mask=%u,%llu,%llu,%d k=%u h=%u slots=%llu "
                "rule=%u m=%llu",
                hex(g.name).c_str(), g.main.log_n, (unsigned long long)g.main.ell,
                (unsigned long long)g.main.r, g.main.over_E ? 1 : 0, g.mask.log_n,
                (unsigned long long)g.mask.ell, (unsigned long long)g.mask.r, g.mask.over_E ? 1 : 0,
                g.k, g.h, (unsigned long long)g.slots, (unsigned)g.rule, (unsigned long long)g.m);
  return b;
}

std::string shape_str(const OracleShape &o) {
  char b[512];
  std::snprintf(b, sizeof b, "name=%s code=%u main_rows=%llu main_deg=%u mask_rows=%llu "
                             "mask_code=%u answers=%u",
                hex(o.name).c_str(), o.code, (unsigned long long)o.main_rows, o.main_deg,
                (unsigned long long)o.mask_rows, o.mask_code, o.answers);
  return b;
}

std::string index_str(const IndexShape &s) {
  char b[512];
  std::snprintf(b, sizeof b,
                "log_n=%u ell=%llu r=%llu v=%u answers=%u salt=%llu radius=%llu later=%llu "
                "m_once=%llu m_later=%llu",
                s.code.log_n, (unsigned long long)s.code.ell, (unsigned long long)s.code.r, s.v,
                s.answers, (unsigned long long)s.salt_bytes,
                (unsigned long long)s.distances.radius, (unsigned long long)s.distances.later_radius,
                (unsigned long long)s.distances.m_once, (unsigned long long)s.distances.m_later);
  return b;
}

std::string table_str(const TableSize &t) {
  char b[512];
  std::snprintf(b, sizeof b,
                "log_n=%u ell=%llu r=%llu v=%u answers=%u radius=%llu later=%llu m_once=%llu "
                "m_later=%llu",
                t.code.log_n, (unsigned long long)t.code.ell, (unsigned long long)t.code.r, t.v,
                t.answers, (unsigned long long)t.distances.radius,
                (unsigned long long)t.distances.later_radius,
                (unsigned long long)t.distances.m_once, (unsigned long long)t.distances.m_later);
  return b;
}

void dump_test(const char *name, const char *test, const TestSizes &x) {
  std::printf("LTEST name=%s test=%s t=%llu group=%s stages=%zu\n", name, test,
              (unsigned long long)x.t, group_str(x.group).c_str(), x.stages.size());
  for (size_t i = 0; i < x.stages.size(); i++)
    std::printf("LSTAGE name=%s test=%s i=%zu t=%llu r_ood=%llu group=%s\n", name, test, i,
                (unsigned long long)x.stages[i].t, (unsigned long long)x.stages[i].r_ood,
                group_str(x.stages[i].g).c_str());
}

void dump_codes(const char *name, const Codes &codes) {
  std::printf("LCODES name=%s base=%zu mask=%zu\n", name, codes.base.size(), codes.mask.size());
  for (size_t i = 0; i < codes.base.size(); i++)
    std::printf("LCODE name=%s kind=base i=%zu log_n=%u ell=%llu r=%llu\n", name, i,
                codes.base[i].log_n, (unsigned long long)codes.base[i].ell,
                (unsigned long long)codes.base[i].r);
  for (size_t i = 0; i < codes.mask.size(); i++)
    std::printf("LCODE name=%s kind=mask i=%zu log_n=%u ell=%llu r=%llu\n", name, i,
                codes.mask[i].log_n, (unsigned long long)codes.mask[i].ell,
                (unsigned long long)codes.mask[i].r);
}

void dump_lin(const char *name, const LinSized &x, const Codes &codes) {
  const LinShape &S = x.S;
  std::printf(
      "LIN name=%s refused=%s k_lo=%u matrix_rows=%llu omega_rh=%d w_rh=%d masks_ahead=%d "
      "ride=%d shared_mask=%u own_mask=%u batches=%llu shared_split=%d own_split=%d columns=%llu "
      "fold_rh=%d omega_lc=%u split_lc=%u w_lc=%u own_lc=%u\n",
      name, hex_or_dash(x.refused).c_str(), S.k_lo, (unsigned long long)S.matrix_rows,
      S.omega_rows_high ? 1 : 0, S.w_rows_high ? 1 : 0, S.masks_ahead ? 1 : 0,
      S.choice.masks_ride ? 1 : 0, S.shared_mask_code, S.own_mask_code,
      (unsigned long long)x.batches, S.shared_split_needed() ? 1 : 0, S.own_split_needed() ? 1 : 0,
      (unsigned long long)S.fold.columns, S.fold.rows_high ? 1 : 0, S.omega_leaf_class,
      S.shared_split_leaf_class, S.w_leaf_class, S.own_split_leaf_class);
  std::printf("LINDEX name=%s %s\n", name, index_str(S.fold.index).c_str());
  std::printf("LSHAPE name=%s at=fold.u %s leaf=%u\n", name, shape_str(S.fold.u).c_str(),
              S.fold.leaf_class);
  std::printf("LSHAPE name=%s at=omega %s\n", name, shape_str(S.omega).c_str());
  std::printf("LSHAPE name=%s at=w %s\n", name, shape_str(S.w).c_str());
  std::printf("LSHAPE name=%s at=shared_split %s\n", name, shape_str(S.shared_split).c_str());
  std::printf("LSHAPE name=%s at=own_split %s\n", name, shape_str(S.own_split).c_str());
  std::printf("LINPUT name=%s %s leaf=%u\n", name, shape_str(x.input.shape).c_str(),
              x.input.leaf_class);
  dump_test(name, "folded", x.folded);
  dump_test(name, "omega", x.omega);
  dump_test(name, "own", x.own);
  std::printf("LSTAGES name=%s test=u n=%zu\n", name, S.test_u.size());
  for (size_t i = 0; i < S.test_u.size(); i++)
    std::printf("LIOPP name=%s test=u i=%zu code=%u mask_code=%u k=%u h=%u\n", name, i,
                S.test_u[i].code, S.test_u[i].mask_code, S.test_u[i].k, S.test_u[i].h);
  std::printf("LSTAGES name=%s test=omega n=%zu\n", name, S.test_omega.size());
  for (size_t i = 0; i < S.test_omega.size(); i++)
    std::printf("LIOPP name=%s test=omega i=%zu code=%u mask_code=%u k=%u h=%u\n", name, i,
                S.test_omega[i].code, S.test_omega[i].mask_code, S.test_omega[i].k,
                S.test_omega[i].h);
  std::printf("LSTAGES name=%s test=own n=%zu\n", name, S.test_own.size());
  for (size_t i = 0; i < S.test_own.size(); i++)
    std::printf("LIOPP name=%s test=own i=%zu code=%u mask_code=%u k=%u h=%u\n", name, i,
                S.test_own[i].code, S.test_own[i].mask_code, S.test_own[i].k, S.test_own[i].h);
  std::printf("LSTAGES name=%s test=own_omega n=%zu\n", name, S.test_own_omega.size());
  for (size_t i = 0; i < S.test_own_omega.size(); i++)
    std::printf("LIOPP name=%s test=own_omega i=%zu code=%u mask_code=%u k=%u h=%u\n", name, i,
                S.test_own_omega[i].code, S.test_own_omega[i].mask_code,
                S.test_own_omega[i].k, S.test_own_omega[i].h);
  std::printf("LTABLE name=%s %s\n", name, table_str(x.table).c_str());
  dump_codes(name, codes);
}

void dump_link(const char *name, const LinkSized &x, const Codes &codes) {
  const LinkShape &S = x.S;
  std::printf(
      "LINK name=%s refused=%s columns_first=%llu columns_further=%llu code=%u mask_code=%u "
      "rows=%llu rows_high=%d leaf_class=%u masks_ahead=%d ride=%d later=%zu\n",
      name, hex_or_dash(x.refused).c_str(), (unsigned long long)S.columns_first,
      (unsigned long long)S.columns_further, S.code, S.mask_code, (unsigned long long)S.rows,
      S.rows_high ? 1 : 0, S.leaf_class, S.masks_ahead ? 1 : 0, S.choice.masks_ride ? 1 : 0,
      S.later.size());
  std::printf("LINDEX name=%s %s\n", name, index_str(S.table).c_str());
  for (size_t i = 0; i < S.later.size(); i++)
    std::printf("LLATER name=%s i=%zu code=%u mask_code=%u k=%u h=%u\n", name, i, S.later[i].code,
                S.later[i].mask_code, S.later[i].k, S.later[i].h);
  dump_test(name, "linked", x.linked);
  std::printf("LTABLE name=%s %s\n", name, table_str(x.table).c_str());
  dump_codes(name, codes);
}

void dump_wf(const char *name, const WfSized &z, const Codes &codes) {
  const WfPublic &x = z.x;
  std::printf(
      "WF name=%s refused=%s k_col=%u rows=%llu pending=%zu message_id=%u ride=%d own_masks=%zu "
      "rows_batched=%llu index_mask_entries=%zu\n",
      name, hex_or_dash(z.refused).c_str(), z.matrix.k_col, (unsigned long long)z.matrix.rows,
      z.pending, x.message_id, x.choice.masks_ride ? 1 : 0, wf_own_masks(x, z.matrix),
      (unsigned long long)wf_rows_batched(x, z.matrix), wf_index_mask_entries(x, z.matrix));
  for (size_t i = 0; i < x.lookups.size(); i++) {
    const WfLookup &l = x.lookups[i];
    std::string weights, bounds;
    for (size_t j = 0; j < l.digit_weight.size(); j++)
      weights += (j ? "," : "") + std::to_string((unsigned long long)l.digit_weight[j].v);
    for (size_t j = 0; j < l.first_bound.size(); j++)
      bounds += (j ? "," : "") + std::to_string(l.first_bound[j]);
    if (weights.empty()) weights = "-";
    if (bounds.empty()) bounds = "-";
    std::printf(
        "WLOOKUP name=%s i=%zu name_hex=%s d=%u mu=%u live=%u weights=%s offset=%llu pad=%llu "
        "first_bound=%s parts=%zu\n",
        name, i, hex(l.name).c_str(), l.d, l.mu, l.live, weights.c_str(),
        (unsigned long long)l.offset.v, (unsigned long long)l.padding_key.v, bounds.c_str(),
        l.parts.size());
    for (size_t j = 0; j < l.parts.size(); j++) {
      std::printf("WPART name=%s i=%zu j=%zu log_places=%u runs=%zu\n", name, i, j,
                  l.parts[j].log_places, l.parts[j].runs.size());
      for (size_t k = 0; k < l.parts[j].runs.size(); k++) {
        const WfRun &r = l.parts[j].runs[k];
        std::printf("WRUN name=%s i=%zu j=%zu k=%zu first_place=%llu first_row=%llu places=%llu "
                    "stride=%llu\n",
                    name, i, j, k, (unsigned long long)r.first_place,
                    (unsigned long long)r.first_row, (unsigned long long)r.places,
                    (unsigned long long)r.stride);
      }
    }
  }
  std::printf("WSHAPE name=%s %s leaf=%u\n", name, shape_str(x.message.shape).c_str(),
              x.message.leaf_class);
  std::printf("WSTAGES name=%s n=%zu\n", name, x.stages.size());
  for (size_t i = 0; i < x.stages.size(); i++)
    std::printf("WIOPP name=%s i=%zu code=%u mask_code=%u k=%u h=%u\n", name, i, x.stages[i].code,
                x.stages[i].mask_code, x.stages[i].k, x.stages[i].h);
  dump_test(name, "test", z.test);
  dump_codes(name, codes);
}

std::string bh(const Big &x) {
  if (x.zero()) return "0";
  std::string s;
  char t[9];
  for (size_t i = 0; i < x.w.size(); i++) {
    std::snprintf(t, sizeof t, "%08x", x.w[i]);
    if (i) s += ",";
    s += t;
  }
  return s;
}

std::string rh(const Real &x) { return bh(x.m) + "@" + std::to_string((long long)x.e); }

unsigned long long dbits(double d) {
  unsigned long long u;
  std::memcpy(&u, &d, sizeof u);
  return u;
}

// The rounds and messages of a finished plan, in plan_emitters_vectors.cpp's format.
void dump_plan(const char *name, const Plan &p) {
  const Planned q = p.finish();
  std::printf("PLAN name=%s\n", name);
  std::printf("VERDICT %d %s\n", (int)q->cause(), hex_or_dash(q->why_not()).c_str());
  for (size_t i = 0; i < q->parts.size(); i++)
    std::printf("PART %zu %s\n", i, hex(q->parts[i]).c_str());
  for (size_t i = 0; i < q->rounds_.size(); i++) {
    const PlanRound &r = q->rounds_[i];
    std::printf(
        "ROUND\t%zu\t%s\t%s\t%d\t%d\t%d\t%s\t%d\t%u\t%llu\t%u\t%zu\t%u\t%u\t%llu\t%llu\t%llu\t%u\t%llu\t%llu\t%llu\t%llu\t%llu\t%d\t"
        "%d\t%u\t%llu\t%llu\t%u\t%llu\t%llu\t%u\t%u\t%llu\t%u\t%llu\t"
        "%d\t%u\t%llu\t%llu\t%u\t%u\t%llu\t%llu\t%llu\t%llu\t%d\n",
        i, hex(r.name).c_str(), hex(r.where).c_str(), (int)r.kind, (int)r.why, (int)r.scope,
        rh(r.error).c_str(), (int)r.rests, r.work_bits, (unsigned long long)r.count, r.part,
        r.message_bytes, r.roots, r.answers, (unsigned long long)r.draw_E,
        (unsigned long long)r.draw_nonzero, (unsigned long long)r.draw_positions, r.log_n,
        (unsigned long long)r.draw_trits, (unsigned long long)r.rows,
        (unsigned long long)r.first_list, (unsigned long long)r.combinations,
        (unsigned long long)r.sharing, (int)r.priced, r.group.said ? 1 : 0, r.group.main.log_n,
        (unsigned long long)r.group.main.ell, (unsigned long long)r.group.main.r,
        r.group.mask.log_n, (unsigned long long)r.group.mask.ell,
        (unsigned long long)r.group.mask.r, r.group.k, r.group.h,
        (unsigned long long)r.group.slots, (unsigned)r.group.rule, (unsigned long long)r.group.m,
        r.table.said ? 1 : 0, r.table.code.log_n, (unsigned long long)r.table.code.ell,
        (unsigned long long)r.table.code.r, r.table.v, r.table.answers,
        (unsigned long long)r.table.distances.radius,
        (unsigned long long)r.table.distances.later_radius,
        (unsigned long long)r.table.distances.m_once,
        (unsigned long long)r.table.distances.m_later, (int)r.table.test);
  }
  for (size_t i = 0; i < q->messages_.size(); i++) {
    const PlanMessage &m = q->messages_[i];
    std::printf("MSG\t%zu\t%s\t%s\t%d\t%llu\t%llx\t%llu\t%u\t%d\t%llu\n", i, hex(m.name).c_str(),
                hex(m.where).c_str(), (int)m.kind, (unsigned long long)m.bytes, dbits(m.expected),
                (unsigned long long)m.count, m.part, m.in_chain ? 1 : 0,
                (unsigned long long)m.hash_calls);
  }
}

TableSize table_of(const Derived &d) { return d.table; }

// The committed table's tree: one symbol of every row in a leaf.
TreeSize table_tree_of(const Setting &s, const Parameters &par) {
  TreeSize t;
  t.name = "table", t.log_n = par.table_log_n, t.leaf_bytes = ((u64)s.f_bytes) << par.table_rows_log;
  return t;
}

// The small explicit layout for WF: a two-digit unit of 4,096 rows and a four-digit unit of 16,384
// rows from row 4,096; the matrix has 65,536 rows.
struct WfUnitLayoutEntry {
  u64 off, rows;
  unsigned nlw;
};
struct WfLayout {
  u64 m0 = 65536;
  std::vector<WfUnitLayoutEntry> U = {{0, 4096, 2}, {4096, 61440, 4}};
};

void dump_lin_cases(const Parameters &p, const Setting &set, const Derived &d) {
  const FrameShape shape = [] {
    FrameShape f;
    f.index_rows = u64(1) << 15;
    return f;
  }();
  {
    Codes codes;
    const LinSized x = lin_sized(set, lin_lines(p, shape, false), table_of(d), codes);
    dump_lin("lin_normal", x, codes);
    if (x.refused.empty()) {
      TreeSize tree = table_tree_of(set, p);
      Plan q(set);
      q.begin_scope(Scope::SHARED);
      lin_plan_shared(q, codes, x, tree);
      plan_seal(q, "seal");
      dump_plan("lin_normal_shared", q);
      Plan r(set);
      r.begin_scope(Scope::REQUEST);
      plan_chain_start(r, "second chain", true);
      lin_plan_second(r, codes, x, tree_sizes(codes, {x.input}));
      plan_seal(r, "seal");
      dump_plan("lin_normal_second", r);
      Plan f(set);
      f.begin_scope(Scope::REQUEST);
      lin_plan_first(f, codes, x);
      plan_seal(f, "seal");
      dump_plan("lin_normal_first", f);
    }
  }
  {
    Codes codes;
    const LinSized x = lin_sized(set, lin_lines(p, shape, true), table_of(d), codes);
    dump_lin("lin_once", x, codes);
    if (x.refused.empty()) {
      TreeSize tree = table_tree_of(set, p);
      Plan q(set);
      q.begin_scope(Scope::ONCE);
      lin_plan_shared(q, codes, x, tree);
      plan_seal(q, "seal");
      dump_plan("lin_once_shared", q);
    }
  }
  {
    // No split: Omega is the folded row's code and a request's group is Omega's.
    LinLines lines = lin_lines(p, shape, false);
    lines.omega = lines.folded;
    lines.own = lines.folded;
    lines.folded.stages = p.omega.stages;
    lines.own.stages = p.omega.stages;
    lines.own.mask_log_ell = 10;
    Codes codes;
    const LinSized x = lin_sized(set, lines, table_of(d), codes);
    dump_lin("lin_no_split", x, codes);
    if (x.refused.empty()) {
      Plan q(set);
      q.begin_scope(Scope::SHARED);
      lin_plan_shared(q, codes, x, table_tree_of(set, p));
      plan_seal(q, "seal");
      dump_plan("lin_no_split_shared", q);
    }
  }
  {
    // A request's mask message with three rows.
    LinLines lines = lin_lines(p, shape, false);
    lines.input_mask_rows = 3;
    Codes codes;
    const LinSized x = lin_sized(set, lines, table_of(d), codes);
    dump_lin("lin_input_three", x, codes);
  }
  {
    // Refusals.
    LinLines lines = lin_lines(p, shape, false);
    lines.own.log_n = p.omega.log_n + 1;
    Codes codes;
    dump_lin("lin_refuse_own", lin_sized(set, lines, table_of(d), codes), codes);
  }
  {
    LinLines lines = lin_lines(p, shape, false);
    lines.folded.mask_log_n = p.omega.mask_log_n + 1;
    Codes codes;
    dump_lin("lin_refuse_split_mask", lin_sized(set, lines, table_of(d), codes), codes);
  }
  {
    TableSize bad = table_of(d);
    bad.distances.radius = bad.code.n();
    bad.distances.later_radius = bad.code.n();
    bad.distances.m_once = 0;
    bad.distances.m_later = 0;
    Codes codes;
    dump_lin("lin_refuse_table", lin_sized(set, lin_lines(p, shape, false), bad, codes), codes);
  }
}

void dump_link_cases(const Parameters &p, const Setting &set, const Derived &d) {
  {
    Codes codes;
    const LinkSized x = link_sized(set, link_lines(p), table_of(d), codes);
    dump_link("link_normal", x, codes);
    if (x.refused.empty()) {
      Plan q(set);
      q.begin_scope(Scope::ONCE);
      link_plan(q, codes, x, table_tree_of(set, p));
      plan_seal(q, "seal");
      dump_plan("link_normal_plan", q);
    }
  }
  {
    // The table's numbers belong to another table.
    LinkLines lines = link_lines(p);
    lines.table_log_n += 1;
    Codes codes;
    dump_link("link_refuse_table", link_sized(set, lines, table_of(d), codes), codes);
  }
  {
    // Distances that are not admitted.
    TableSize bad = table_of(d);
    bad.distances.radius = bad.code.n();
    bad.distances.later_radius = bad.code.n();
    bad.distances.m_once = 0;
    bad.distances.m_later = 0;
    Codes codes;
    dump_link("link_refuse_distance", link_sized(set, link_lines(p), bad, codes), codes);
  }
}

void dump_wf_cases(const Parameters &p, const Setting &set) {
  const WfLayout Y;
  const WfShape shape = wf_shape_of_layout(Y, p.block_log);
  {
    Codes codes;
    const WfLines lines = wf_lines(shape, p.once_ranges, p.ranges_part);
    const WfSized z = wf_sized(set, lines, codes);
    dump_wf("wf_normal", z, codes);
    if (z.refused.empty()) {
      Plan q(set);
      q.begin_scope(Scope::ONCE);
      wf_plan(q, codes, z);
      plan_seal(q, "seal");
      dump_plan("wf_normal_plan", q);
    }
  }
  {
    // More parts than the limit allows.
    Codes codes;
    const WfLines lines = wf_lines(shape, p.once_ranges, 6);
    dump_wf("wf_refuse_parts", wf_sized(set, lines, codes), codes);
  }
  {
    // A part would read more rows than the matrix has.
    Codes codes;
    const WfLines lines = wf_lines(shape, p.once_ranges, 17);
    dump_wf("wf_refuse_part_rows", wf_sized(set, lines, codes), codes);
  }
  {
    // wf_lines rejects lookups that already have planes.
    WfShape bad = shape;
    bad.lookups[0].lookup.mu = 1;
    Codes codes;
    const WfLines lines = wf_lines(bad, p.once_ranges, p.ranges_part);
    dump_wf("wf_refuse_planes", wf_sized(set, lines, codes), codes);
  }
  {
    // No look-up.
    WfShape empty;
    empty.k_col = p.block_log;
    empty.matrix_rows = Y.m0;
    Codes codes;
    const WfLines lines = wf_lines(empty, p.once_ranges, p.ranges_part);
    dump_wf("wf_refuse_empty", wf_sized(set, lines, codes), codes);
  }
}

// A focused req_plan(): a small synthetic setting, one code, three segments and a sub-plan that
// changes the scope.
void dump_req_plan_case() {
  Setting set = setting_goldilocks();
  set.target = 32;
  set.samples = 1;

  Codes codes;
  GroupSize link_group;
  link_group.name = "link";
  link_group.main.name = "link";
  link_group.main.log_n = 8, link_group.main.ell = 64, link_group.main.r = 2;
  link_group.mask.name = "link mask";
  link_group.mask.log_n = 8, link_group.mask.ell = 64, link_group.mask.r = 2, link_group.mask.over_E = true;
  link_group.k = 1, link_group.h = 1;

  TestSizes sized;
  sized.group = link_group;
  std::string why;
  {
    GroupLoad load;
    load.cube_bits = stage_cube_bits(link_group);
    load.messages = 1, load.batched_rows = 4;
    solve_group(set, Scope::REQUEST, load, [](u64 t) { return t; }, sized, why);
  }
  {
    Plan scratch(set);
    const std::vector<Stage> stages =
        solve_stages(scratch, sized.group, sized.t, {StageChoice{0, 0, 12, 12}});
    sized.stages = stages;
  }
  const std::vector<IoppStage> last_stages = iopp_stages(sized.stages, codes);

  ReqShape s;
  s.code = 0, s.mask_code = 0, s.answers = 1;
  s.choice.masks_ride = true;
  s.last = last_stages;
  {
    ReqLink first;
    first.name = "first";
    ReqMessage a;
    a.shape.name = "a";
    a.shape.code = 0, a.shape.main_rows = 1, a.shape.main_deg = 3;
    a.shape.answers = 1, a.leaf_class = 0, a.moment = 0, a.life = 1;
    first.messages.push_back(a);
    ReqLink second;
    second.name = "second";
    ReqMessage b;
    b.shape.name = "b";
    b.shape.code = 0, b.shape.main_rows = 0, b.shape.mask_rows = 1, b.shape.mask_code = 0;
    b.shape.answers = 1, b.leaf_class = 1, b.moment = 0, b.life = 0;
    ReqMessage c = b;
    c.moment = 1;
    second.messages.push_back(b);
    second.messages.push_back(c);
    s.link = {first, second};
  }

  ReqSizes z;
  z.group = sized.group;
  z.last = sized.stages;
  z.rows = {3, 4};

  Plan p(set);
  const ReqSubPlan sub = [](Plan &q, size_t, unsigned) {
    q.begin_scope(Scope::SHARED);
    plan_none(q, R_REPLY, "sub");
  };
  req_plan(p, codes, s, z, sub);
  plan_seal(p, "seal");
  dump_plan("req_plan", p);

  // What rides at the start, and plain scalars: the riders are priced with z.at_start's list size.
  {
    ReqShape t = s;
    OracleShape masks;
    masks.name = "masks", masks.main_rows = 0, masks.mask_rows = 1, masks.mask_code = 0,
    masks.answers = 1;
    t.at_start.push_back(OracleNotice{masks, 2});
    t.link[0].plain = 2;
    ReqSizes zr = z;
    zr.at_start = sized.group;
    zr.at_start.name = "at start";
    Plan q(set);
    req_plan(q, codes, t, zr, sub);
    plan_seal(q, "seal");
    dump_plan("req_plan_riders", q);
  }
}

}  // namespace

int main(int argc, char **argv) {
  if (argc != 2) {
    std::fprintf(stderr, "usage: frame_sizes_vectors <policy.txt>\n");
    return 2;
  }
  std::ifstream f(argv[1], std::ios::binary);
  if (!f) {
    std::fprintf(stderr, "frame_sizes_vectors: cannot read %s\n", argv[1]);
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
  const Setting &set = d.set;
  std::printf("DERIVED refused=%s table=%s\n", hex_or_dash(d.refused).c_str(),
              table_str(d.table).c_str());
  dump_lin_cases(p, set, d);
  dump_link_cases(p, set, d);
  dump_wf_cases(p, set);
  dump_req_plan_case();
  return 0;
}
