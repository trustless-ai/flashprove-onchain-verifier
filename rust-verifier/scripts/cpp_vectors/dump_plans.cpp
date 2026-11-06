// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Dumps the finished plans and their accounting for the example configuration. It links
// verifier/src/cp_verify.cpp compiled with -DCP_VERIFY_AS_A_UNIT and calls cp_with_configured(),
// so the plans are the ones the C++ verifier itself makes. It changes no C++ source.
//
// Build (from the repository root):
//   clang++ -O2 -std=c++17 -pthread -Iverifier/src -Iblocks -Iprover \
//     -DBLK_FIELD=2 -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
//     -DVF_SOURCE_DIGEST='"93af..."' -DCP_VERIFY_AS_A_UNIT -c verifier/src/cp_verify.cpp -o /tmp/cp_verify_unit.o
//   clang++ ... -c rust-verifier/scripts/cpp_vectors/dump_plans.cpp -o /tmp/dump_plans.o
//   clang++ /tmp/dump_plans.o /tmp/cp_verify_unit.o -pthread -o /tmp/dump_plans
//
// Usage: dump_plans <policy.txt> <layout.txt> <KL.bin>
// Output: tab-separated lines documented in fp-core/src/numbers/plan.rs (reader) and in the Rust
// test fp-host/tests/numbers_golden.rs.

#include "cp_configured.h"

#include "frame/files.h"
#include "numbers/accounting.h"

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <string>
#include <utility>
#include <vector>

using namespace blk;

namespace {
std::string read_bytes(const char *path) {
  std::ifstream f(path, std::ios::binary);
  if (!f) {
    std::fprintf(stderr, "dump_plans: cannot read %s\n", path);
    std::exit(2);
  }
  return std::string(std::istreambuf_iterator<char>(f), std::istreambuf_iterator<char>());
}

std::vector<u32> read_words(const char *path) {
  const std::string b = read_bytes(path);
  if (b.size() % 4) {
    std::fprintf(stderr, "dump_plans: %s is not a whole number of words\n", path);
    std::exit(2);
  }
  std::vector<u32> w(b.size() / 4);
  for (size_t i = 0; i < w.size(); i++)
    w[i] = (u32)(u8)b[4 * i] | (u32)(u8)b[4 * i + 1] << 8 | (u32)(u8)b[4 * i + 2] << 16 |
           (u32)(u8)b[4 * i + 3] << 24;
  return w;
}

std::string big_hex(const Big &x) {
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

std::string real_str(const Real &x) { return big_hex(x.m) + "@" + std::to_string(x.e); }

void dump_setting(const Setting &s) {
  std::printf(
      "SETTING\t%s\t%s\t%u\t%d\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%llu\t%u\t%d",
      s.field_name.c_str(), big_hex(s.p).c_str(), s.degree, (int)s.circle, s.f_bytes, s.e_bytes,
      s.digest_bytes, s.salt_bytes, s.nonce_bytes, s.position_bytes, s.hash_block_bytes,
      s.label_bytes, s.chain_extra_bytes, s.chain_free_words, s.target,
      (unsigned long long)s.instances, s.samples, (int)s.saved_coefficient);
  for (int i = 0; i < 6; i++)
    for (int j = 0; j < 3; j++) std::printf("\t%u", s.work[i][j]);
  std::printf("\n");
}

void dump_round(const PlanRound &r) {
  const PricedGroup &g = r.group;
  const PricedTable &t = r.table;
  std::printf(
      "ROUND\t%s\t%s\t%d\t%d\t%d\t%s\t%d\t%u\t%llu\t%u\t%zu\t%u\t%u"
      "\t%llu\t%llu\t%llu\t%u\t%llu\t%llu\t%llu\t%llu\t%llu\t%d"
      "\t%u\t%llu\t%llu\t%u\t%llu\t%llu\t%u\t%u\t%llu\t%d\t%u\t%llu"
      "\t%u\t%llu\t%llu\t%u\t%u\t%llu\t%llu\t%llu\t%llu\t%d\t%d",
      r.name.c_str(), r.where.c_str(), (int)r.kind, (int)r.why, (int)r.scope,
      real_str(r.error).c_str(), (int)r.rests, r.work_bits, (unsigned long long)r.count, r.part,
      r.message_bytes, r.roots, r.answers, (unsigned long long)r.draw_E,
      (unsigned long long)r.draw_nonzero, (unsigned long long)r.draw_positions, r.log_n,
      (unsigned long long)r.draw_trits, (unsigned long long)r.rows,
      (unsigned long long)r.first_list, (unsigned long long)r.combinations,
      (unsigned long long)r.sharing, (int)r.priced,
      g.main.log_n, (unsigned long long)g.main.ell, (unsigned long long)g.main.r, g.mask.log_n,
      (unsigned long long)g.mask.ell, (unsigned long long)g.mask.r, g.k, g.h,
      (unsigned long long)g.slots, (int)g.said, g.rule, (unsigned long long)g.m,
      t.code.log_n, (unsigned long long)t.code.ell, (unsigned long long)t.code.r, t.v, t.answers,
      (unsigned long long)t.distances.radius, (unsigned long long)t.distances.later_radius,
      (unsigned long long)t.distances.m_once, (unsigned long long)t.distances.m_later,
      (int)t.said, (int)t.test);
  std::printf("\n");
}

void dump_message(const PlanMessage &m) {
  std::printf("MESSAGE\t%s\t%s\t%d\t%llu\t%.17g\t%llu\t%u\t%d\t%llu\n", m.name.c_str(),
              m.where.c_str(), (int)m.kind, (unsigned long long)m.bytes, m.expected,
              (unsigned long long)m.count, m.part, (int)m.in_chain,
              (unsigned long long)m.hash_calls);
}

void dump_account(const char *file, const Accounting &a) {
  const AccountGroup &g = a.groups.empty() ? a.lists : a.groups[0];
  std::printf(
      "ACCOUNT\t%s\t%d\t%d\t%d\t%u\t%u\t%llu\t%llu\t%zu\t%.17g\t%u\t%llu\t%s\t%d\t%d\t%.17g\t%u\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%.17g\t%.17g\t%llu\t%llu\t%.17g\t%u\t%llu\n",
      file, (int)a.formed, (int)a.holds, (int)a.needs_work, a.target, a.digest_bits,
      (unsigned long long)a.rounds, (unsigned long long)a.queries, a.groups.size(), g.bits, g.work,
      (unsigned long long)g.rounds, g.name.c_str(), (int)g.holds, (int)g.list, a.lists.bits,
      a.lists.work, (unsigned long long)a.closeness[0], (unsigned long long)a.closeness[1],
      (unsigned long long)a.by_work, (unsigned long long)a.near,
      (unsigned long long)a.near_small, (unsigned long long)a.near_closeness[0],
      (unsigned long long)a.near_closeness[1], a.sum, a.sum_lists,
      (unsigned long long)a.planned_calls, (unsigned long long)a.small_columns,
      a.small_union.all(), a.small_union.work, (unsigned long long)a.on_a_word);
}

int dump(const Configured &c) {
  if (!c.refused().empty()) {
    std::fprintf(stderr, "dump_plans: the configuration was refused: %s\n", c.refused().c_str());
    return 1;
  }
  const Setting &s = c.sized().d.set;
  dump_setting(s);
  const std::pair<const char *, const FilePlan *> files[] = {
      {"key", &c.key()}, {"entry", &c.entry()}, {"proof", &c.proof()}};
  for (const auto &f : files) {
    const Planned whole = merged(s, {*f.second});
    std::printf("PLAN\t%s\t%zu\n", f.first, whole->parts.size());
    for (const std::string &p : whole->parts) std::printf("PART\t%s\n", p.c_str());
    for (const PlanRound &r : whole->rounds_) dump_round(r);
    for (const PlanMessage &m : whole->messages_) dump_message(m);
    dump_account(f.first, account(whole));
  }
  {
    const Planned whole = merged(s, {c.key(), c.entry(), c.proof()});
    std::printf("PLAN\tall\t%zu\n", whole->parts.size());
    for (const std::string &p : whole->parts) std::printf("PART\t%s\n", p.c_str());
    for (const PlanRound &r : whole->rounds_) dump_round(r);
    for (const PlanMessage &m : whole->messages_) dump_message(m);
    dump_account("all", account(whole));
  }
  return 0;
}
} // namespace

int main(int argc, char **argv) {
  if (argc != 4) {
    std::fprintf(stderr, "usage: dump_plans <policy.txt> <layout.txt> <KL.bin>\n");
    return 2;
  }
  const std::string policy = read_bytes(argv[1]);
  const std::string layout = read_bytes(argv[2]);
  const std::vector<u32> kl = read_words(argv[3]);
  return cp_with_configured(policy, layout, kl, 128.0, true, dump);
}
