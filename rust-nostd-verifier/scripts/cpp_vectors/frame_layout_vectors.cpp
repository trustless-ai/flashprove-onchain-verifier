// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for `layout_read` (`blocks/frame/req_frame.h:74-104`), generated from the accepted
// configuration's layout.txt. Each case prints the input (hex), the accepted flag, the rejection
// text (hex), and every parsed group and block, so the Rust test replays it byte for byte.
//
// Usage: frame_layout_vectors <layout.txt>

#include <cstdio>
#include <fstream>
#include <string>
#include <vector>

#include "frame/req_frame.h"

using namespace blk;

static std::string hex(const std::string &s) {
  static const char *d = "0123456789abcdef";
  std::string o;
  o.reserve(2 * s.size());
  for (unsigned char c : s) o += d[c >> 4], o += d[c & 15];
  return o;
}

static void dump(const char *name, const std::string &text) {
  LayoutLines L;
  const char *why = layout_read(text, L);
  std::printf("LAYOUT name=%s input=%s ok=%d why=%s groups=%zu blocks=%zu\n", name,
              hex(text).c_str(), why ? 0 : 1, why ? hex(why).c_str() : "-", L.groups.size(),
              L.blocks.size());
  for (const LayoutGroup &g : L.groups)
    std::printf("LG link=%u moment=%u group=%u cls=%c rows=%llu life=%u\n", g.link, g.moment,
                g.group, g.cls, (unsigned long long)g.rows, g.life);
  for (const LayoutBlock &b : L.blocks)
    std::printf("LB link=%u moment=%u group=%u array=%u first_i=%llu bits_i=%u first_c=%llu "
                "bits_c=%u i_is_low=%d first_row=%llu first_place=%llu row_bits=%u place_bits=%u\n",
                b.link, b.moment, b.group, b.array, (unsigned long long)b.at.first_i, b.at.bits_i,
                (unsigned long long)b.at.first_c, b.at.bits_c, b.at.i_is_low ? 1 : 0,
                (unsigned long long)b.at.first_row, (unsigned long long)b.at.first_place,
                b.at.row_bits, b.at.place_bits);
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
    std::fprintf(stderr, "usage: frame_layout_vectors <layout.txt>\n");
    return 2;
  }
  std::ifstream f(argv[1], std::ios::binary);
  if (!f) {
    std::fprintf(stderr, "frame_layout_vectors: cannot read %s\n", argv[1]);
    return 2;
  }
  const std::string whole((std::istreambuf_iterator<char>(f)), std::istreambuf_iterator<char>());
  const std::vector<std::string> L = lines_of(whole);
  if (L.size() < 3) {
    std::fprintf(stderr, "frame_layout_vectors: %s has %zu lines, want at least 3\n", argv[1],
                 L.size());
    return 2;
  }
  dump("full", whole);
  dump("empty", "");
  dump("blank_line", join([&] {
         std::vector<std::string> x = L;
         x.insert(x.begin(), "");
         return x;
       }()));
  dump("comment_line", join([&] {
         std::vector<std::string> x = L;
         x.insert(x.begin(), "# another comment");
         return x;
       }()));
  dump("space_comment", join([&] {
         std::vector<std::string> x = L;
         x.insert(x.begin(), "   # not a comment: it starts with a space");
         return x;
       }()));
  dump("group_leading_space", with_line(L, 1, " 1 1 1 N 61 0"));
  dump("group_plus_sign", with_line(L, 1, "+1 +1 +1 N 61 0"));
  dump("group_leading_zero", with_line(L, 1, "01 01 01 N 61 0"));
  dump("group_class_x", with_line(L, 1, "1 1 1 X 61 0"));
  dump("group_rows_zero", with_line(L, 1, "1 1 1 N 0 0"));
  dump("group_life_on_n", with_line(L, 1, "1 1 1 N 61 2"));
  dump("group_b_life_zero", with_line(L, 1, "1 1 1 B 61 0"));
  dump("group_link_zero", with_line(L, 1, "0 1 1 N 61 0"));
  dump("group_link_big", with_line(L, 1, "1048576 1 1 N 61 0"));
  dump("group_trailing", with_line(L, 1, "1 1 1 N 61 0 7"));
  dump("group_crlf", with_line(L, 1, "1 1 1 N 61 0\r"));
  dump("group_short", with_line(L, 1, "1 1 1 N 61"));
  dump("block_letter_x", with_line(L, 2, "1 1 1 5 0 11 0 10 x 0 0 5 16 0"));
  dump("block_last_one", with_line(L, 2, "1 1 1 5 0 11 0 10 r 0 0 5 16 1"));
  dump("block_link_zero", with_line(L, 2, "0 1 1 5 0 11 0 10 r 0 0 5 16 0"));
  dump("block_bits_48", with_line(L, 2, "1 1 1 5 0 48 0 10 r 0 0 5 16 0"));
  dump("block_short", with_line(L, 2, "1 1 1 5 0 11 0 10 r 0 0 5 16"));
  dump("block_trailing", with_line(L, 2, "1 1 1 5 0 11 0 10 r 0 0 5 16 0 9"));
  dump("text_line", with_line(L, 2, "not a line"));
  return 0;
}
