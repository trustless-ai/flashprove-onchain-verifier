// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the strict parameter parser (`blocks/frame/parameters.h`), generated from a real
// policy.txt. Each case prints the accepted flag, the exact rejection text (hex, spaces included),
// every parsed field, and the whole `rest`, so the Rust test replays them byte for byte.
//
// Usage: frame_parameters_vectors <policy.txt>

#include <cstdio>
#include <fstream>
#include <string>
#include <vector>

#include "frame/parameters.h"

using namespace blk;

static std::string hex(const std::string &s) {
  static const char *d = "0123456789abcdef";
  std::string o;
  o.reserve(2 * s.size());
  for (unsigned char c : s) {
    o += d[c >> 4];
    o += d[c & 15];
  }
  return o;
}

static std::string group_str(const GroupLine &g) {
  char b[160];
  std::string o;
  std::snprintf(b, sizeof b, "%u,%u,%u,%u", g.log_n, g.log_ell, g.mask_log_n, g.mask_log_ell);
  o += b;
  for (const StageChoice &s : g.stages) {
    std::snprintf(b, sizeof b, ";%u,%u,%u,%u", s.k, s.h, s.log_n, s.mask_log_n);
    o += b;
  }
  return o;
}

static void dump(const char *name, const std::string &text) {
  Parameters p;
  std::string why;
  const bool ok = read_parameters(text, p, why);
  std::printf("PARAM name=%s input=%s ok=%d why=%s version=%08x sec=%u slots=%llu answers=%u salt=%u "
              "ranges_part=%u rows=%u n=%u block=%u data=%llu random=%llu work=",
              name, hex(text).c_str(), ok ? 1 : 0, why.empty() ? "-" : hex(why).c_str(),
              p.version, p.sec,
              (unsigned long long)p.slots, p.answers, p.salt, p.ranges_part, p.table_rows_log,
              p.table_log_n, p.block_log, (unsigned long long)p.table_data,
              (unsigned long long)p.table_random);
  for (int k = 0; k < 5; k++)
    for (int s = 0; s < 3; s++) std::printf("%s%u", k || s ? "," : "", p.work[k][s]);
  std::printf(" groups=%s|%s|%s|%s|%s|%s|%s|%s rest=%s\n", group_str(p.link).c_str(),
              group_str(p.folded).c_str(), group_str(p.omega).c_str(), group_str(p.own).c_str(),
              group_str(p.once_folded).c_str(), group_str(p.once_omega).c_str(),
              group_str(p.once_own).c_str(), group_str(p.once_ranges).c_str(), hex(p.rest).c_str());
}

static std::vector<std::string> lines_of(const std::string &t) {
  std::vector<std::string> v;
  for (size_t a = 0; a < t.size();) {
    const size_t e = t.find('\n', a);
    v.push_back(t.substr(a, e == std::string::npos ? e : e - a));
    if (e == std::string::npos) break;
    a = e + 1;
  }
  return v;
}

static std::string join(const std::vector<std::string> &v) {
  std::string t;
  for (const std::string &l : v) t += l + "\n";
  return t;
}

static std::string with_line(const std::vector<std::string> &v, size_t i, const std::string &l) {
  std::vector<std::string> x = v;
  x[i] = l;
  return join(x);
}

int main(int argc, char **argv) {
  if (argc != 2) {
    std::fprintf(stderr, "usage: frame_parameters_vectors <policy.txt>\n");
    return 2;
  }
  std::ifstream f(argv[1], std::ios::binary);
  if (!f) {
    std::fprintf(stderr, "frame_parameters_vectors: cannot read %s\n", argv[1]);
    return 2;
  }
  const std::string whole((std::istreambuf_iterator<char>(f)), std::istreambuf_iterator<char>());
  const std::vector<std::string> L = lines_of(whole);
  if (L.size() < 34) {
    std::fprintf(stderr, "frame_parameters_vectors: %s has %zu lines, want at least 34\n", argv[1],
                 L.size());
    return 2;
  }
  dump("full", whole);

  // One line replaced at a time. The accepted file's frame is lines 0..33 (version .. table).
  dump("version_bad", with_line(L, 0, "version H820"));
  dump("version_short", with_line(L, 0, "version H82"));
  dump("version_crlf", with_line(L, 0, "version H821\r"));
  dump("sec_zero", with_line(L, 1, "sec 0"));
  dump("sec_above", with_line(L, 1, "sec 257"));
  dump("sec_leading_zero", with_line(L, 1, "sec 0128"));
  dump("sec_long", with_line(L, 1, "sec 0000000000000001"));
  dump("sec_non_digit", with_line(L, 1, "sec 12x"));
  dump("line_blank", with_line(L, 1, ""));
  dump("line_two_spaces", with_line(L, 1, "sec  128"));
  dump("line_missing_value", with_line(L, 1, "sec"));
  dump("line_extra_value", with_line(L, 1, "sec 128 1"));
  dump("reading_zero", with_line(L, 2, "reading 0"));
  dump("rowcost_zero", with_line(L, 3, "rowcost 0"));
  dump("slots_three", with_line(L, 4, "slots 3"));
  dump("answers_two", with_line(L, 5, "answers 2"));
  dump("record_zero", with_line(L, 6, "record 0"));
  dump("work_field_59", with_line(L, 7, "work field 59 0 0"));
  dump("work_field_at_sec", with_line(L, 7, "work field 128 0 0"));
  dump("salt_39", with_line(L, 12, "salt 39"));
  dump("salt_41", with_line(L, 12, "salt 41"));
  dump("listed_one", with_line(L, 13, "listed 1"));
  dump("group_link_j2", with_line(L, 14, "group link 2 18 17 17 13"));
  dump("group_link_n33", with_line(L, 14, "group link 1 33 17 17 13"));
  dump("group_link_ell_eq_n", with_line(L, 14, "group link 1 18 18 17 13"));
  dump("group_link_mask_n_big", with_line(L, 14, "group link 1 18 17 19 13"));
  dump("group_link_mask_ell_eq", with_line(L, 14, "group link 1 18 17 17 17"));
  dump("stages_link_count", with_line(L, 15, "stages link 4 3"));
  dump("stages_link_many", with_line(L, 15, [] {
         std::string s = "stages link";
         for (int i = 0; i < 36; i++) s += i % 4 == 0 ? " 1" : " 0";
         return s;
       }()));
  dump("stages_link_k9", with_line(L, 15, "stages link 9 3 17 17 3 3 16 16 3 3 15 15 0 0 15 15"));
  dump("stages_link_h_gt_k", with_line(L, 15, "stages link 4 5 17 17 3 3 16 16 3 3 15 15 0 0 15 15"));
  dump("stages_link_n33", with_line(L, 15, "stages link 4 3 33 17 3 3 16 16 3 3 15 15 0 0 15 15"));
  dump("stages_link_nz_gt_n", with_line(L, 15, "stages link 4 3 17 18 3 3 16 16 3 3 15 15 0 0 15 15"));
  dump("stages_link_last_k", with_line(L, 15, "stages link 4 3 17 17 3 3 16 16 3 3 15 15 1 0 15 15"));
  dump("stages_link_middle_k0", with_line(L, 15, "stages link 4 3 17 17 0 3 16 16 3 3 15 15 0 0 15 15"));
  dump("ranges_part_zero", with_line(L, 32, "ranges-part 0"));
  dump("ranges_part_41", with_line(L, 32, "ranges-part 41"));
  dump("table_rows_21", with_line(L, 33, "table 21 23 524288 65535 0 11"));
  dump("table_n_33", with_line(L, 33, "table 8 33 524288 65535 0 11"));
  dump("table_data_zero", with_line(L, 33, "table 8 23 0 65535 0 11"));
  dump("table_data_random_big", with_line(L, 33, "table 8 23 8388608 0 0 11"));
  dump("table_e_nonzero", with_line(L, 33, "table 8 23 524288 65535 1 11"));
  dump("table_block_41", with_line(L, 33, "table 8 23 524288 65535 0 41"));
  dump("table_block_lt_rows", with_line(L, 33, "table 8 23 524288 65535 0 7"));
  dump("own_code_mismatch", with_line(L, 21, "group own 1 18 13 13 8"));
  dump("one_mask_code_mismatch", with_line(L, 16, "group folded 1 17 15 12 6"));
  {
    std::vector<std::string> cut(L.begin(), L.begin() + 33);
    dump("table_missing", join(cut));
  }
  {
    std::vector<std::string> lead = L;
    lead.insert(lead.begin(), "");
    dump("leading_blank_line", join(lead));
  }
  return 0;
}
