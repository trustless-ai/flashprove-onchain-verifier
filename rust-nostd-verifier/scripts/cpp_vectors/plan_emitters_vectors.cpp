// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Deterministic vectors for the plan emitters of blocks/numbers/blocks.h: the `plan_*` functions
// that append rounds and messages to a Plan. Each case builds a Plan by hand from small shapes and
// dumps every field of its finished rounds and messages; fp-host/tests/plan_emitters_vectors.rs
// replays the same cases through the Rust port and compares. It changes no source of the C++
// headers.
//
// Build (from the repository root):
//   clang++ -O2 -std=c++17 -Iblocks -DBLK_FIELD=2 -o /tmp/plan_emitters_vectors \
//     rust-nostd-verifier/scripts/cpp_vectors/plan_emitters_vectors.cpp
// Run: /tmp/plan_emitters_vectors > rust-nostd-verifier/fixtures/plan_emitters_vectors.txt
//
// Line format (tab-separated): CASE, SETTING, VERDICT, PART, ROUND, MSG. The reader in
// fp-host/tests/plan_emitters_vectors.rs documents the fields.

#include "numbers/blocks.h"

#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

using namespace blk;

namespace {

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

void dump_setting(const Setting &s) {
  std::printf("SETTING\t%s\t%s\t%u\t%d\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%llu\t%u\t%d",
              s.field_name.c_str(), bh(s.p).c_str(), s.degree, (int)s.circle, s.f_bytes, s.e_bytes,
              s.digest_bytes, s.salt_bytes, s.nonce_bytes, s.position_bytes, s.hash_block_bytes,
              s.label_bytes, s.chain_extra_bytes, s.chain_free_words, s.target,
              (unsigned long long)s.instances, s.samples, (int)s.saved_coefficient);
  for (int i = 0; i < 6; i++)
    for (int j = 0; j < 3; j++) std::printf("\t%u", s.work[i][j]);
  std::printf("\n");
}

void dump(const char *name, const Plan &p) {
  const Planned q = p.finish();
  std::printf("CASE\t%s\n", name);
  dump_setting(q->set);
  std::printf("VERDICT\t%d\t%s\n", (int)q->cause(), q->why_not().c_str());
  for (size_t i = 0; i < q->parts.size(); i++)
    std::printf("PART\t%zu\t%s\n", i, q->parts[i].c_str());
  for (size_t i = 0; i < q->rounds_.size(); i++) {
    const PlanRound &r = q->rounds_[i];
    std::printf(
        "ROUND\t%zu\t%s\t%s\t%d\t%d\t%d\t%s\t%d\t%u\t%llu\t%u\t%zu\t%u\t%u\t%llu\t%llu\t%llu\t%u\t%llu\t%llu\t%llu\t%llu\t%llu\t%d\t"
        "%d\t%u\t%llu\t%llu\t%u\t%llu\t%llu\t%u\t%u\t%llu\t%u\t%llu\t"
        "%d\t%u\t%llu\t%llu\t%u\t%u\t%llu\t%llu\t%llu\t%llu\t%d\n",
        i, r.name.c_str(), r.where.c_str(), (int)r.kind, (int)r.why, (int)r.scope,
        rh(r.error).c_str(), (int)r.rests, r.work_bits, (unsigned long long)r.count, r.part,
        r.message_bytes, r.roots, r.answers, (unsigned long long)r.draw_E,
        (unsigned long long)r.draw_nonzero, (unsigned long long)r.draw_positions, r.log_n,
        (unsigned long long)r.draw_trits, (unsigned long long)r.rows,
        (unsigned long long)r.first_list, (unsigned long long)r.combinations,
        (unsigned long long)r.sharing, (int)r.priced,
        r.group.said ? 1 : 0, r.group.main.log_n, (unsigned long long)r.group.main.ell,
        (unsigned long long)r.group.main.r, r.group.mask.log_n,
        (unsigned long long)r.group.mask.ell, (unsigned long long)r.group.mask.r, r.group.k,
        r.group.h, (unsigned long long)r.group.slots, r.group.rule,
        (unsigned long long)r.group.m,
        r.table.said ? 1 : 0, r.table.code.log_n, (unsigned long long)r.table.code.ell,
        (unsigned long long)r.table.code.r, r.table.v, r.table.answers,
        (unsigned long long)r.table.distances.radius,
        (unsigned long long)r.table.distances.later_radius,
        (unsigned long long)r.table.distances.m_once,
        (unsigned long long)r.table.distances.m_later, (int)r.table.test);
  }
  for (size_t i = 0; i < q->messages_.size(); i++) {
    const PlanMessage &m = q->messages_[i];
    std::printf("MSG\t%zu\t%s\t%s\t%d\t%llu\t%llx\t%llu\t%u\t%d\t%llu\n", i, m.name.c_str(),
                m.where.c_str(), (int)m.kind, (unsigned long long)m.bytes, dbits(m.expected),
                (unsigned long long)m.count, m.part, m.in_chain ? 1 : 0,
                (unsigned long long)m.hash_calls);
  }
}

Setting small() {
  Setting s = setting_goldilocks();
  s.target = 32;
  return s;
}

CodeSize C(unsigned log_n, uint64_t ell, uint64_t r) {
  CodeSize c;
  c.log_n = log_n;
  c.ell = ell;
  c.r = r;
  return c;
}

GroupSize G(const char *name, CodeSize main, CodeSize mask, unsigned k, unsigned h, uint64_t slots) {
  GroupSize g;
  g.name = name;
  g.main = main;
  g.mask = mask;
  g.k = k;
  g.h = h;
  g.slots = slots;
  return g;
}

GroupSize plain_shape(const char *name) { return G(name, C(4, 4, 4), CodeSize(), 0, 0, 1); }

GroupSize masked_shape(const char *name) { return G(name, C(4, 8, 4), C(4, 4, 2), 3, 1, 1); }

GroupSize sized(const Setting &s, const GroupSize &shape) {
  return size_group(s, Scope::REQUEST, shape, GroupLoad());
}

TableSize table_small() {
  TableSize t;
  t.code = C(4, 4, 0);
  t.v = 3;
  t.answers = 1;
  t.distances.radius = 4;
  t.distances.later_radius = 2;
  return t;
}

void case_send() {
  Setting s = small();
  s.samples = 2;
  const GroupSize plain = sized(s, plain_shape("plain"));
  const GroupSize masked = sized(s, masked_shape("masked"));
  Plan p(s);
  plan_send(p, "send", {SampleSize{5, TestedIn(plain)}, SampleSize{8, TestedIn(plain, masked)}}, 2, true);
  plan_chain_start(p, "start", true);
  plan_file_item(p, "header", "the file", MessageKind::HEAD, 128, 128.0, 3);
  plan_bat_sigma(p, "sigma", 4);
  Plan sub(s);
  plan_bat_sigma(sub, "sub", 2);
  const Planned subf = sub.finish();
  p.begin_part("key");
  p.push_repeat(2);
  plan_chain(p, subf);
  p.pop_repeat();
  p.begin_part("proof");
  plan_none(p, R_LAST, "last");
  dump("send", p);
}

void case_bat() {
  const Setting s = small();
  const GroupSize plain = sized(s, plain_shape("plain"));
  const GroupSize masked = sized(s, masked_shape("masked"));
  Plan p(s);
  p.compact = true;
  plan_bat(p, "bat", TestedIn(plain, masked), 5);
  plan_bat_sigma(p, "sigma", 7);
  plan_split(p, "split");
  dump("bat", p);
}

void case_psc() {
  const Setting s = small();
  Plan p(s);
  p.compact = true;
  PscSize x;
  x.degree = {3, 3, 2, 2};
  x.degree_Y = 2;
  x.values = 2;
  plan_psc(p, "psc", x);
  PscSize y;
  y.degree = {3, 3};
  y.with_Y = false;
  plan_psc(p, "psc affine", y);
  plan_zero(p, "zero", 4);
  plan_line(p, "line");
  plan_shift(p, "shift", 9);
  plan_join(p, "join", 3);
  plan_lkp(p, "lkp", 5);
  plan_product_tree(p, "tree", 2, 1);
  plan_batt(p, "batt", 6, 3);
  dump("psc", p);
}

void case_psc_open_coeff() {
  Setting s = small();
  s.saved_coefficient = false;
  Plan p(s);
  p.compact = true;
  PscSize x;
  x.degree = {3, 1};
  x.degree_Y = 3;
  x.values = 1;
  plan_psc(p, "psc open", x);
  plan_batt(p, "batt", 5, 2);
  dump("psc_open_coeff", p);
}

void case_lookup() {
  const Setting s = small();
  Plan p(s);
  p.compact = true;
  LookupSize x;
  x.v = 4;
  x.d = 3;
  x.mu = 3;
  x.shifted = true;
  x.live = 0;
  x.parts = {2, 2};
  plan_lookup(p, "lookup", x);
  LookupSize y;
  y.v = 1;
  y.d = 2;
  y.mu = 3;
  y.live = 2;
  plan_lookup(p, "lookup small", y);
  LookupSize z;
  z.v = 2;
  z.d = 2;
  z.mu = 0;
  plan_lookup(p, "lookup refused", z);
  dump("lookup", p);
}

void case_rng() {
  Setting s = small();
  s.set_work(ErrorKind::SMALL, Scope::REQUEST, 5);
  Plan p(s);
  plan_rng(p, "rng", 10);
  dump("rng", p);

  Plan q(s);
  plan_rng(q, "rng too many", ~(uint64_t)0);
  dump("rng_refuse", q);
}

void case_fold() {
  const Setting s = small();
  const GroupSize plain = sized(s, plain_shape("plain"));
  const GroupSize masked = sized(s, masked_shape("masked"));
  const GroupSize nomask = sized(s, G("fold nomask", C(4, 8, 4), CodeSize(), 3, 0, 1));
  Plan p(s);
  p.compact = true;
  plan_fold(p, "fold masked", masked, 1);
  plan_fold(p, "fold nomask", nomask, 0);
  plan_fold(p, "fold plain", plain, 0);
  TreeSize tr;
  tr.name = "leaves";
  tr.log_n = 4;
  tr.leaf_bytes = 64;
  plan_loc(p, "loc", masked, {tr});
  plan_base(p, "base", plain, {tr}, 1);
  dump("fold", p);
}

void case_cs() {
  const Setting s = small();
  const GroupSize plain = sized(s, plain_shape("plain"));
  const GroupSize masked = sized(s, masked_shape("masked"));
  Plan p(s);
  TreeSize tr;
  tr.name = "old rows";
  tr.log_n = 4;
  tr.leaf_bytes = 64;
  plan_cs(p, "cs", plain, masked, 6, 1, 2, {tr}, 1);
  plan_base(p, "base", masked, {tr}, 1);
  dump("cs", p);
}

void case_iopp(const char *name, bool masks_ride) {
  const Setting s = small();
  const GroupSize masked = sized(s, masked_shape("test"));
  Plan p(s);
  const uint64_t t1 = plan_positions(p, analysis(s, masked).at.agree);
  const std::vector<Stage> st =
      solve_stages(p, masked, t1, {StageChoice{1, 1, 8, 8}, StageChoice{0, 0, 12, 12}});
  TreeSize tr;
  tr.name = "first";
  tr.log_n = 4;
  tr.leaf_bytes = 64;
  plan_iopp(p, "iopp", st, {tr}, 3, 1, masks_ride);
  dump(name, p);
}

void case_record() {
  const Setting s = small();
  Plan p(s);
  plan_record(p, "record", table_small());
  plan_seal(p, "seal");
  dump("record", p);

  TableSize T = table_small();
  T.answers = 0;
  Plan q(s);
  plan_record(q, "record zero", T);
  dump("record_zero", q);
}

void case_lin() {
  const Setting s = small();
  const GroupSize plain = sized(s, plain_shape("plain"));
  LinSize x{SampleSize{5, TestedIn(plain)}, SampleSize{6, TestedIn(plain)},
            SampleSize{7, TestedIn(plain)}};
  x.instances = 2;
  x.k_lo = 2;
  x.rows_log = 3;
  x.one_time = true;
  x.beside_w.push_back(SampleSize{4, TestedIn(plain)});
  x.beside_omega.push_back(SampleSize{4, TestedIn(plain)});
  x.roots_w = 2;
  x.roots_u = 1;
  x.roots_omega = 2;
  Plan p(s);
  plan_lin_first(p, "lin", x);
  TreeSize tr;
  tr.name = "lin table";
  tr.log_n = 4;
  tr.leaf_bytes = 64;
  plan_lin_shared(p, "lin", table_small(), x, tr);
  plan_seal(p, "seal");
  dump("lin", p);
}

void case_link() {
  const Setting s = small();
  const GroupSize plain = sized(s, plain_shape("plain"));
  const SampleSize u{5, TestedIn(plain)};
  TreeSize tr;
  tr.name = "link table";
  tr.log_n = 4;
  tr.leaf_bytes = 64;
  Plan p(s);
  uint64_t a = 0, b = 0;
  plan_link(p, "link", table_small(), u, tr, a, b);
  plan_seal(p, "seal");
  dump("link", p);
}

void case_instances() {
  Setting s = small();
  s.instances = 3;
  s.samples = 2;
  s.set_work(ErrorKind::FIELD, Scope::REQUEST, 8);
  s.set_work(ErrorKind::FIELD, Scope::SHARED, 4);
  const GroupSize plain = sized(s, plain_shape("plain"));
  Plan p(s);
  plan_bat(p, "bat request", TestedIn(plain), 5);
  p.begin_scope(Scope::SHARED);
  plan_bat(p, "bat shared", TestedIn(plain), 5);
  p.begin_scope(Scope::ONCE);
  plan_bat(p, "bat once", TestedIn(plain), 5);
  p.begin_scope(Scope::REQUEST);
  plan_send(p, "send", {SampleSize{5, TestedIn(plain)}}, 1);
  plan_rng(p, "rng", 3);
  dump("instances", p);
}

void case_at_rule() {
  const Setting s = small();
  const GroupSize g = group_at(plain_shape("at"), 4);
  Plan p(s);
  plan_fold(p, "fold at", g, 0);
  plan_loc(p, "loc at", g, {});
  dump("at_rule", p);
}

}  // namespace

int main() {
  case_send();
  case_bat();
  case_psc();
  case_psc_open_coeff();
  case_lookup();
  case_rng();
  case_fold();
  case_cs();
  case_iopp("iopp", false);
  case_iopp("iopp_ride", true);
  case_record();
  case_lin();
  case_link();
  case_instances();
  case_at_rule();
  return 0;
}
