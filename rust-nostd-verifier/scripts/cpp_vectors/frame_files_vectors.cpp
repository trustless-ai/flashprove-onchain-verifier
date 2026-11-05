// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the plans of the three files a verifier reads:
//   Subproofs, stand_in_subproofs(), frame_shape_of(), sized(), file_proof(), file_key(),
//   file_entry(), merged() (blocks/frame/files.h) and KeyFixed, key_fixed(), key_public_bytes(),
//   key_fault() (blocks/frame/key_fixed.h).
//
// Usage: frame_files_vectors <policy.txt> [<parameters-that-the-stand-in-fits.txt>]
//
// The first file is the accepted policy parameter file; with the stand-in sub-proofs its table is
// too small, so `sized` refuses and every file's chains are rejected plans with the same reason.
// That path is dumped in full: the derived sizes, the request and every refusal.
//
// If a second parameter file is given, the same flow runs on it with `compact = true` plans. The
// example `blocks/frame/examples/record.f2.txt` (copied to fixtures/config-standin/policy.txt) is
// one whose table the stand-in fits, so the second half dumps every round and message that
// `file_proof`, `file_key`, `file_entry` and `merged` make.
//
// `fp-host/tests/frame_files_vectors.rs` rebuilds both halves with the port and renders the same
// lines. The `OneList` counter: the C++ headers keep it in a static; the port passes a fresh
// counter per file. The numbers are never printed.

#include <cstdio>
#include <cstring>
#include <fstream>
#include <string>
#include <utility>
#include <vector>

#include "frame/files.h"
#include "frame/heads.h"
#include "frame/key_fixed.h"
#include "hash/hash.h"

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

std::string bytes_hex(const std::vector<u8> &v) {
  static const char *d = "0123456789abcdef";
  std::string o;
  o.reserve(2 * v.size());
  for (u8 c : v) o += d[c >> 4], o += d[c & 15];
  return o;
}

std::string digest_hex(const Digest &x) {
  u8 b[DIGEST_BYTES];
  digest_to_bytes(x, b);
  return bytes_hex(std::vector<u8>(b, b + DIGEST_BYTES));
}

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

void dump_test(const std::string &name, const char *test, const TestSizes &x) {
  std::printf("LTEST name=%s test=%s t=%llu group=%s stages=%zu\n", name.c_str(), test,
              (unsigned long long)x.t, group_str(x.group).c_str(), x.stages.size());
  for (size_t i = 0; i < x.stages.size(); i++)
    std::printf("LSTAGE name=%s test=%s i=%zu t=%llu r_ood=%llu group=%s\n", name.c_str(), test, i,
                (unsigned long long)x.stages[i].t, (unsigned long long)x.stages[i].r_ood,
                group_str(x.stages[i].g).c_str());
}

void dump_codes(const std::string &name, const Codes &codes) {
  std::printf("LCODES name=%s base=%zu mask=%zu\n", name.c_str(), codes.base.size(),
              codes.mask.size());
  for (size_t i = 0; i < codes.base.size(); i++)
    std::printf("LCODE name=%s kind=base i=%zu log_n=%u ell=%llu r=%llu\n", name.c_str(), i,
                codes.base[i].log_n, (unsigned long long)codes.base[i].ell,
                (unsigned long long)codes.base[i].r);
  for (size_t i = 0; i < codes.mask.size(); i++)
    std::printf("LCODE name=%s kind=mask i=%zu log_n=%u ell=%llu r=%llu\n", name.c_str(), i,
                codes.mask[i].log_n, (unsigned long long)codes.mask[i].ell,
                (unsigned long long)codes.mask[i].r);
}

// The oracle-message shapes and the four tests of a LinShape.
void dump_lin_members(const std::string &name, const LinShape &S) {
  std::printf("LINDEX name=%s %s\n", name.c_str(), index_str(S.fold.index).c_str());
  std::printf("LSHAPE name=%s at=fold.u %s leaf=%u\n", name.c_str(),
              shape_str(S.fold.u).c_str(), S.fold.leaf_class);
  std::printf("LSHAPE name=%s at=omega %s\n", name.c_str(), shape_str(S.omega).c_str());
  std::printf("LSHAPE name=%s at=w %s\n", name.c_str(), shape_str(S.w).c_str());
  std::printf("LSHAPE name=%s at=shared_split %s\n", name.c_str(),
              shape_str(S.shared_split).c_str());
  std::printf("LSHAPE name=%s at=own_split %s\n", name.c_str(), shape_str(S.own_split).c_str());
  for (std::pair<const char *, const std::vector<IoppStage> *> t :
       {std::make_pair("u", &S.test_u), std::make_pair("omega", &S.test_omega),
        std::make_pair("own", &S.test_own), std::make_pair("own_omega", &S.test_own_omega)}) {
    std::printf("LSTAGES name=%s test=%s n=%zu\n", name.c_str(), t.first, t.second->size());
    for (size_t i = 0; i < t.second->size(); i++)
      std::printf("LIOPP name=%s test=%s i=%zu code=%u mask_code=%u k=%u h=%u\n", name.c_str(),
                  t.first, i, (*t.second)[i].code, (*t.second)[i].mask_code, (*t.second)[i].k,
                  (*t.second)[i].h);
  }
}

void dump_lin(const std::string &name, const LinSized &x, const Codes &codes) {
  const LinShape &S = x.S;
  std::printf(
      "LIN name=%s refused=%s k_lo=%u matrix_rows=%llu omega_rh=%d w_rh=%d masks_ahead=%d "
      "ride=%d shared_mask=%u own_mask=%u batches=%llu shared_split=%d own_split=%d columns=%llu "
      "fold_rh=%d omega_lc=%u split_lc=%u w_lc=%u own_lc=%u\n",
      name.c_str(), hex_or_dash(x.refused).c_str(), S.k_lo, (unsigned long long)S.matrix_rows,
      S.omega_rows_high ? 1 : 0, S.w_rows_high ? 1 : 0, S.masks_ahead ? 1 : 0,
      S.choice.masks_ride ? 1 : 0, S.shared_mask_code, S.own_mask_code,
      (unsigned long long)x.batches, S.shared_split_needed() ? 1 : 0, S.own_split_needed() ? 1 : 0,
      (unsigned long long)S.fold.columns, S.fold.rows_high ? 1 : 0, S.omega_leaf_class,
      S.shared_split_leaf_class, S.w_leaf_class, S.own_split_leaf_class);
  dump_lin_members(name, S);
  std::printf("LINPUT name=%s %s leaf=%u\n", name.c_str(), shape_str(x.input.shape).c_str(),
              x.input.leaf_class);
  dump_test(name, "folded", x.folded);
  dump_test(name, "omega", x.omega);
  dump_test(name, "own", x.own);
  std::printf("LTABLE name=%s %s\n", name.c_str(), table_str(x.table).c_str());
  dump_codes(name, codes);
}

void dump_link(const std::string &name, const LinkSized &x, const Codes &codes) {
  const LinkShape &S = x.S;
  std::printf(
      "LINK name=%s refused=%s columns_first=%llu columns_further=%llu code=%u mask_code=%u "
      "rows=%llu rows_high=%d leaf_class=%u masks_ahead=%d ride=%d later=%zu\n",
      name.c_str(), hex_or_dash(x.refused).c_str(), (unsigned long long)S.columns_first,
      (unsigned long long)S.columns_further, S.code, S.mask_code, (unsigned long long)S.rows,
      S.rows_high ? 1 : 0, S.leaf_class, S.masks_ahead ? 1 : 0, S.choice.masks_ride ? 1 : 0,
      S.later.size());
  std::printf("LINDEX name=%s %s\n", name.c_str(), index_str(S.table).c_str());
  for (size_t i = 0; i < S.later.size(); i++)
    std::printf("LLATER name=%s i=%zu code=%u mask_code=%u k=%u h=%u\n", name.c_str(), i,
                S.later[i].code, S.later[i].mask_code, S.later[i].k, S.later[i].h);
  dump_test(name, "linked", x.linked);
  std::printf("LTABLE name=%s %s\n", name.c_str(), table_str(x.table).c_str());
  dump_codes(name, codes);
}

void dump_wf_public(const std::string &name, const WfPublic &x) {
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
        name.c_str(), i, hex(l.name).c_str(), l.d, l.mu, l.live, weights.c_str(),
        (unsigned long long)l.offset.v, (unsigned long long)l.padding_key.v, bounds.c_str(),
        l.parts.size());
    for (size_t j = 0; j < l.parts.size(); j++) {
      std::printf("WPART name=%s i=%zu j=%zu log_places=%u runs=%zu\n", name.c_str(), i, j,
                  l.parts[j].log_places, l.parts[j].runs.size());
      for (size_t k = 0; k < l.parts[j].runs.size(); k++) {
        const WfRun &r = l.parts[j].runs[k];
        std::printf("WRUN name=%s i=%zu j=%zu k=%zu first_place=%llu first_row=%llu places=%llu "
                    "stride=%llu\n",
                    name.c_str(), i, j, k, (unsigned long long)r.first_place,
                    (unsigned long long)r.first_row, (unsigned long long)r.places,
                    (unsigned long long)r.stride);
      }
    }
  }
  std::printf("WSHAPE name=%s %s leaf=%u\n", name.c_str(), shape_str(x.message.shape).c_str(),
              x.message.leaf_class);
  std::printf("WSTAGES name=%s n=%zu\n", name.c_str(), x.stages.size());
  for (size_t i = 0; i < x.stages.size(); i++)
    std::printf("WIOPP name=%s i=%zu code=%u mask_code=%u k=%u h=%u\n", name.c_str(), i,
                x.stages[i].code, x.stages[i].mask_code, x.stages[i].k, x.stages[i].h);
  std::printf("WCHOICE name=%s ride=%d\n", name.c_str(), x.choice.masks_ride ? 1 : 0);
}

void dump_wf(const std::string &name, const WfSized &z, const Codes &codes) {
  const WfPublic &x = z.x;
  std::printf(
      "WF name=%s refused=%s k_col=%u rows=%llu pending=%zu message_id=%u ride=%d own_masks=%zu "
      "rows_batched=%llu index_mask_entries=%zu\n",
      name.c_str(), hex_or_dash(z.refused).c_str(), z.matrix.k_col,
      (unsigned long long)z.matrix.rows, z.pending, x.message_id, x.choice.masks_ride ? 1 : 0,
      wf_own_masks(x, z.matrix), (unsigned long long)wf_rows_batched(x, z.matrix),
      wf_index_mask_entries(x, z.matrix));
  dump_wf_public(name, x);
  dump_test(name, "test", z.test);
  dump_codes(name, codes);
}

void dump_request(const std::string &name, const ReqShape &s) {
  std::printf("REQUEST name=%s code=%u mask_code=%u answers=%u links=%zu at_start=%zu last=%zu "
              "ride=%d\n",
              name.c_str(), s.code, s.mask_code, s.answers, s.link.size(), s.at_start.size(),
              s.last.size(), s.choice.masks_ride ? 1 : 0);
  for (size_t i = 0; i < s.at_start.size(); i++)
    std::printf("QSTART name=%s i=%zu %s leaf=%u\n", name.c_str(), i,
                shape_str(s.at_start[i].shape).c_str(), s.at_start[i].leaf_class);
  for (size_t i = 0; i < s.link.size(); i++) {
    std::printf("QLINK name=%s i=%zu name_hex=%s plain=%u messages=%zu\n", name.c_str(), i,
                hex(s.link[i].name).c_str(), s.link[i].plain, s.link[i].messages.size());
    for (size_t j = 0; j < s.link[i].messages.size(); j++) {
      const ReqMessage &m = s.link[i].messages[j];
      std::printf("QMSG name=%s i=%zu j=%zu name_hex=%s code=%u main_rows=%llu main_deg=%u "
                  "mask_rows=%llu mask_code=%u answers=%u leaf=%u moment=%u life=%u\n",
                  name.c_str(), i, j, hex(m.shape.name).c_str(), m.shape.code,
                  (unsigned long long)m.shape.main_rows, m.shape.main_deg,
                  (unsigned long long)m.shape.mask_rows, m.shape.mask_code, m.shape.answers,
                  m.leaf_class, m.moment, m.life);
    }
  }
  for (size_t i = 0; i < s.last.size(); i++)
    std::printf("QLAST name=%s i=%zu code=%u mask_code=%u k=%u h=%u\n", name.c_str(), i,
                s.last[i].code, s.last[i].mask_code, s.last[i].k, s.last[i].h);
}

void dump_subproofs(const std::string &name, const Subproofs &sub) {
  dump_request(name + "/request", sub.request);
  std::string rows;
  for (size_t i = 0; i < sub.open_rows.size(); i++)
    rows += (i ? "," : "") + std::to_string((unsigned long long)sub.open_rows[i]);
  std::printf("SUB name=%s open_rows=%zu open_rows_list=%s pending=%llu ranges_k_col=%u "
              "ranges_rows=%llu ranges_lookups=%zu\n",
              name.c_str(), sub.open_rows.size(), rows.c_str(),
              (unsigned long long)sub.pending_rows, sub.ranges.k_col,
              (unsigned long long)sub.ranges.matrix_rows, sub.ranges.lookups.size());
  for (size_t i = 0; i < sub.ranges.lookups.size(); i++) {
    const WfShapeLookup &l = sub.ranges.lookups[i];
    std::string weights, bounds;
    for (size_t j = 0; j < l.lookup.digit_weight.size(); j++)
      weights += (j ? "," : "") + std::to_string((unsigned long long)l.lookup.digit_weight[j].v);
    for (size_t j = 0; j < l.lookup.first_bound.size(); j++)
      bounds += (j ? "," : "") + std::to_string(l.lookup.first_bound[j]);
    if (weights.empty()) weights = "-";
    if (bounds.empty()) bounds = "-";
    std::printf("SUBL name=%s i=%zu name_hex=%s d=%u weights=%s offset=%llu first_bound=%s "
                "log_rows_apart=%u entries=%zu\n",
                name.c_str(), i, hex(l.lookup.name).c_str(), l.lookup.d, weights.c_str(),
                (unsigned long long)l.lookup.offset.v, bounds.c_str(), l.log_rows_apart,
                l.entries.size());
    for (size_t j = 0; j < l.entries.size(); j++)
      std::printf("SUBRUN name=%s i=%zu j=%zu first_place=%llu first_row=%llu places=%llu "
                  "stride=%llu\n",
                  name.c_str(), i, j, (unsigned long long)l.entries[j].first_place,
                  (unsigned long long)l.entries[j].first_row,
                  (unsigned long long)l.entries[j].places,
                  (unsigned long long)l.entries[j].stride);
  }
}

void dump_sized(const std::string &name, const Sized &z) {
  std::printf("SIZED name=%s refused=%s\n", name.c_str(), hex_or_dash(z.refused).c_str());
  dump_request(name + "/request", z.request);
  std::printf("SDERIVED name=%s refused=%s table=%s\n", name.c_str(),
              hex_or_dash(z.d.refused).c_str(), table_str(z.d.table).c_str());
  dump_test(name, "link", z.d.link);
  dump_test(name, "last", z.d.last);
  dump_lin(name + "/batch", z.batch, z.proof_codes);
  dump_lin(name + "/once", z.once, z.key_codes);
  dump_wf(name + "/ranges", z.ranges, z.key_codes);
  dump_link(name + "/link", z.link, z.entry_codes);
  dump_codes(name + "/proof_codes", z.proof_codes);
  dump_codes(name + "/key_codes", z.key_codes);
  dump_codes(name + "/entry_codes", z.entry_codes);
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

// The rounds and messages of a finished plan, in plan_emitters_vectors.cpp's format, with the
// parts' sizes and the plan's count of queries.
void dump_planned(const std::string &name, const Planned &q) {
  std::printf("PLAN name=%s\n", name.c_str());
  std::printf("VERDICT %d %s\n", (int)q->cause(), hex_or_dash(q->why_not()).c_str());
  std::printf("QUERIES %llu\n", (unsigned long long)q->queries());
  for (size_t i = 0; i < q->parts.size(); i++)
    std::printf("PART %zu %s\n", i, hex(q->parts[i]).c_str());
  for (size_t i = 0; i < q->parts.size(); i++) {
    const PartSize s = q->size_of((unsigned)i);
    std::printf("PSIZE %zu %llu %llx\n", i, (unsigned long long)s.bytes, dbits(s.expected));
  }
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

void dump_file(const std::string &label, const FilePlan &f) {
  std::printf("FILE label=%s name=%s head_words=%u place_depth=%u has_place=%d chains=%zu\n",
              label.c_str(), hex(f.name).c_str(), f.head_words, f.place_depth,
              f.has_place ? 1 : 0, f.chains.size());
  for (size_t i = 0; i < f.chains.size(); i++) {
    std::printf("CHAIN label=%s file=%s i=%zu name_hex=%s\n", label.c_str(), hex(f.name).c_str(),
                i, hex(f.chains[i].name).c_str());
    dump_planned(label + "/" + f.name + "/" + f.chains[i].name, f.chains[i].plan);
  }
}

void dump_key_fault_case(const std::string &name, const char *what, const KeyFixed &f) {
  const char *why = key_fault(f);
  std::printf("KEYFAULT2 name=%s case=%s fault=%s\n", name.c_str(), what,
              why ? hex(why).c_str() : "-");
}

// The later checks of key_fault(): one field broken at a time on a key that otherwise passes.
void dump_key_fault_cases(const std::string &name, const KeyFixed &base) {
  dump_key_fault_case(name, "base", base);
  {
    KeyFixed f = base;
    f.lin.matrix_rows = 0;
    dump_key_fault_case(name, "lin", f);
  }
  {
    KeyFixed f = base;
    f.ranges.lookups.clear();
    dump_key_fault_case(name, "ranges", f);
  }
  {
    KeyFixed f = base;
    f.binding.log_leaves = 1;
    dump_key_fault_case(name, "binding", f);
  }
  {
    KeyFixed f = base;
    f.ranges.message_id = 0;
    dump_key_fault_case(name, "message_id", f);
  }
  {
    KeyFixed f = base;
    f.index_masks.shape.main_rows = 1;
    dump_key_fault_case(name, "mask_main_rows", f);
  }
  {
    KeyFixed f = base;
    f.index_masks.shape.mask_rows = 0;
    dump_key_fault_case(name, "mask_no_rows", f);
  }
  {
    KeyFixed f = base;
    f.index_masks.shape.answers = 0;
    dump_key_fault_case(name, "mask_no_answers", f);
  }
  {
    KeyFixed f = base;
    f.index_masks.shape.mask_code = (unsigned)f.codes.mask.size();
    dump_key_fault_case(name, "mask_code", f);
  }
  {
    KeyFixed f = base;
    f.index_masks.shape.mask_rows = 1;
    // A base whose codes are empty (a refused key) still gives a deterministic case.
    const unsigned code = f.index_masks.shape.mask_code;
    f.index_masks.shape.answers =
        f.codes.mask.empty() ? 1u
                             : (unsigned)f.codes.mask[code < f.codes.mask.size() ? code : 0].ell;
    dump_key_fault_case(name, "mask_no_room", f);
  }
}

void dump_key(const std::string &name, const KeyFixed &f) {
  std::printf("KEY name=%s configuration=%s binding_log_leaves=%u binding_salt_bytes=%llu\n",
              name.c_str(), digest_hex(f.configuration).c_str(), f.binding.log_leaves,
              (unsigned long long)f.binding.salt_bytes);
  dump_codes(name + "/codes", f.codes);
  const LinShape &S = f.lin;
  std::printf(
      "KEYLIN name=%s k_lo=%u matrix_rows=%llu omega_rh=%d w_rh=%d masks_ahead=%d ride=%d "
      "shared_mask=%u own_mask=%u shared_split=%d own_split=%d columns=%llu fold_rh=%d "
      "omega_lc=%u split_lc=%u w_lc=%u own_lc=%u\n",
      name.c_str(), S.k_lo, (unsigned long long)S.matrix_rows, S.omega_rows_high ? 1 : 0,
      S.w_rows_high ? 1 : 0, S.masks_ahead ? 1 : 0, S.choice.masks_ride ? 1 : 0,
      S.shared_mask_code, S.own_mask_code, S.shared_split_needed() ? 1 : 0,
      S.own_split_needed() ? 1 : 0, (unsigned long long)S.fold.columns,
      S.fold.rows_high ? 1 : 0, S.omega_leaf_class, S.shared_split_leaf_class, S.w_leaf_class,
      S.own_split_leaf_class);
  dump_lin_members(name + "/lin", S);
  std::printf("KEYMASKS name=%s %s leaf=%u\n", name.c_str(),
              shape_str(f.index_masks.shape).c_str(), f.index_masks.leaf_class);
  dump_wf_public(name + "/ranges", f.ranges);
  const std::vector<u8> bytes = key_public_bytes(f);
  std::printf("KEYBYTES name=%s n=%zu %s\n", name.c_str(), bytes.size(),
              bytes_hex(bytes).c_str());
  const char *fault = key_fault(f);
  std::printf("KEYFAULT name=%s %s\n", name.c_str(), fault ? hex(fault).c_str() : "-");
}

// One whole flow on one parameter file.
void run(const std::string &label, const Parameters &par, const std::string &text,
         bool compact) {
  const FrameShape shape;
  const Derived d = derive(par, shape);
  std::printf("DERIVED name=%s refused=%s table=%s\n", label.c_str(),
              hex_or_dash(d.refused).c_str(), table_str(d.table).c_str());
  dump_test(label, "link", d.link);
  dump_test(label, "last", d.last);

  const Subproofs sub = stand_in_subproofs();
  dump_subproofs(label + "/stand_in", sub);

  const Sized z = sized(par, sub);
  dump_sized(label + "/sized", z);

  const FilePlan proof = file_proof(z, sub, compact);
  const FilePlan key = file_key(z, compact);
  const FilePlan entry = file_entry(z, compact);
  dump_file(label + "/sized", proof);
  dump_file(label + "/sized", key);
  dump_file(label + "/sized", entry);
  dump_planned(label + "/sized/merged", merged(z.d.set, {proof, key, entry}));

  const Digest configuration = parameter_file_digest(text);
  const KeyFixed fixed = key_fixed(z, configuration);
  dump_key(label + "/key", fixed);
  dump_key_fault_cases(label + "/key", fixed);
}

bool read_file(const char *path, std::string &text) {
  std::ifstream f(path, std::ios::binary);
  if (!f) return false;
  text.assign((std::istreambuf_iterator<char>(f)), std::istreambuf_iterator<char>());
  return true;
}

}  // namespace

int main(int argc, char **argv) {
  if (argc != 2 && argc != 3) {
    std::fprintf(stderr, "usage: frame_files_vectors <policy.txt> [<fit-parameters.txt>]\n");
    return 2;
  }
  {
    std::string text;
    Parameters par;
    std::string why;
    if (!read_file(argv[1], text)) {
      std::fprintf(stderr, "frame_files_vectors: cannot read %s\n", argv[1]);
      return 2;
    }
    if (!read_parameters(text, par, why)) {
      std::printf("PARAMS name=policy read=0 why=%s\n", hex(why).c_str());
      return 0;
    }
    std::printf("PARAMS name=policy read=1\n");
    run("policy", par, text, false);
  }
  if (argc == 3) {
    std::string text;
    Parameters par;
    std::string why;
    if (!read_file(argv[2], text)) {
      std::fprintf(stderr, "frame_files_vectors: cannot read %s\n", argv[2]);
      return 2;
    }
    if (!read_parameters(text, par, why)) {
      std::printf("PARAMS name=fit read=0 why=%s\n", hex(why).c_str());
      return 0;
    }
    std::printf("PARAMS name=fit read=1\n");
    run("fit", par, text, true);
  }
  return 0;
}
