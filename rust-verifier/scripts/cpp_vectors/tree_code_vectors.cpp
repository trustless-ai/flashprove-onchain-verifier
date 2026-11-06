// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for blocks/tree/ (TreeShape, tree_walk, TreeValues, Opening, read/write/check) and
// blocks/code/ (points, factors, generator rows, symbols, Encoder, short positions). Build with
// -DBLK_FIELD=2.

#include "code/code.h"
#include "code/cosets.h"
#include "code/short_position.h"
#include "hash/hash.h"
#include "iop/message.h"
#include "tree/opening.h"
#include "tree/positions.h"
#include "tree/tree.h"

#include <cstdio>
#include <map>
#include <vector>

using namespace blk;

namespace {
Digest make_digest(u32 seed) {
  Digest d{};
  for (int i = 0; i < 8; i++) d.w[i] = seed * 0x9E3779B9u + (u32)i * 0x85EBCA6Bu;
  return d;
}
void pd(const char *name, const Digest &d) {
  std::printf("%s=", name);
  for (int i = 0; i < 8; i++) std::printf("%08x", d.w[i]);
}
void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
void pf(F x) { std::printf("%016llx", (unsigned long long)x.v); }
void phex(const std::vector<u8> &b) {
  if (b.empty()) std::printf("-");
  for (u8 x : b) std::printf("%02x", x);
}
F col_f(u64 pos, size_t j) { return F{1000 + pos * 17 + (u64)j * 3}; }
u8 salt_byte(u64 pos, size_t k) { return (u8)((pos * 31 + k * 7 + 5) & 0xFF); }

struct Side {
  using Value = Digest;
  const TreeShape &shape;
  Tag tag;
  const PositionList &list;
  const std::vector<Digest> &leaves; // by position
  std::vector<Digest> &given_out;
  const std::map<u64, Digest> &values;
  Value leaf(size_t i) { return leaves[list[i]]; }
  bool given(unsigned d, u64 p, Value &v) {
    auto it = values.find(tree_index(d, p));
    if (it == values.end()) return false;
    v = it->second;
    given_out.push_back(v);
    return true;
  }
  Value node(unsigned, u64, const Value &l, const Value &r) { return vertex(tag, l, r); }
};

size_t tree_case(int ci, const std::vector<u64> &draws, int li) {
  const OracleTreeShape s = [] {
    OracleTreeShape x;
    x.log_n = 3;
    x.log_n_zk = 2;
    x.main_symbols = {2};
    x.mask_symbols = {1};
    x.tree_number = 7;
    x.salt_bytes = 40;
    x.stored = false;
    x.run = make_digest(10);
    x.parameters = make_digest(11);
    return x;
  }();
  const unsigned n = (unsigned)1 << s.log_n;
  const PositionList list = PositionList::from_draws(draws, s.log_n);
  std::vector<F> cols(n * s.width());
  std::vector<u8> salts(n * s.salt_bytes);
  std::vector<Digest> leaves(n);
  for (u64 pos = 0; pos < n; pos++) {
    for (size_t j = 0; j < s.width(); j++) cols[pos * s.width() + j] = col_f(pos, j);
    for (size_t k = 0; k < s.salt_bytes; k++) salts[pos * s.salt_bytes + k] = salt_byte(pos, k);
    leaves[pos] = oracle_leaf(s, pos, cols.data() + pos * s.width(), s.width(), salts.data() + pos * s.salt_bytes);
  }
  const TreeShape shape = s.tree();
  const Tag tag = shape.vertex_tag();
  std::map<u64, Digest> values;
  for (u64 pos = 0; pos < n; pos++) values[tree_index(s.log_n, pos)] = leaves[pos];
  for (unsigned d = s.log_n; d > 0; d--)
    for (u64 p = 0; p < ((u64)1 << (d - 1)); p++)
      values[tree_index(d - 1, p)] =
          vertex(tag, values[tree_index(d, 2 * p)], values[tree_index(d, 2 * p + 1)]);
  const Digest root = values[tree_index(0, 0)];

  std::vector<Digest> given;
  Side side{shape, tag, list, leaves, given, values};
  Digest walked{};
  const bool led = tree_walk(shape, list, side, walked);

  Opening o;
  o.main_width = s.main_width();
  o.mask_width = s.mask_width();
  for (size_t i = 0; i < list.size(); i++) {
    const u64 pos = list[i];
    for (size_t j = 0; j < s.width(); j++) o.columns.push_back(cols[pos * s.width() + j]);
    o.salts.insert(o.salts.end(), salts.begin() + pos * s.salt_bytes, salts.begin() + (pos + 1) * s.salt_bytes);
  }
  o.given = given;
  Writer w;
  write_opening(w, s, list, o);
  Reader r(w.data(), w.size());
  Opening back;
  const bool read = read_opening(r, s, list, back);
  const bool at_end = r.at_end();
  TreeValues seen;
  bool clash = false;
  const bool checked = check_opening(root, s, list, back, &seen, &clash);
  const size_t vertices = seen.vertices();
  const u64 entered = seen.entered();

  std::printf("TREE%d log_n=%u log_n_zk=%u main=%zu mask=%zu tree_number=%u salt_bytes=%zu width=%zu ",
              ci, s.log_n, s.log_n_zk, (size_t)s.main_width(), (size_t)s.mask_width(), s.tree_number, s.salt_bytes,
              s.width());
  pd("run", s.run);
  pd(" params", s.parameters);
  pd(" root", root);
  std::printf(" given=%zu opening_bytes=%zu\n", given.size(), opening_bytes(s, list));
  for (u64 pos = 0; pos < n; pos++) {
    std::printf("COLS%d pos=%llu f=", ci, (unsigned long long)pos);
    for (size_t j = 0; j < s.width(); j++) std::printf("%s%016llx", j ? "," : "", (unsigned long long)cols[pos * s.width() + j].v);
    std::printf(" salt=");
    phex(std::vector<u8>(salts.begin() + pos * s.salt_bytes, salts.begin() + (pos + 1) * s.salt_bytes));
    pd(" leaf", leaves[pos]);
    std::printf("\n");
  }
  std::printf("LIST%d i=%d log_n=%u draws=", ci, li, list.log_n());
  for (size_t i = 0; i < list.draws().size(); i++) std::printf("%s%llu", i ? "," : "", (unsigned long long)list.draws()[i]);
  std::printf(" led=%d", (int)led);
  pd(" walked", walked);
  std::printf(" given=%zu gn=%zu read=%d at_end=%d check=%d clash=%d vertices=%zu entered=%llu\n",
              o.given.size(), opening_given(s, list), (int)read, (int)at_end, (int)checked, (int)clash, vertices,
              (unsigned long long)entered);
  std::printf("OPENING%d i=%d ", ci, li);
  phex(w.bytes());
  std::printf("\n");
  return vertices;
}
} // namespace

int main() {
  tree_case(0, {0, 2, 5, 7}, 0);
  tree_case(1, {1, 1, 6}, 1);
  tree_case(2, {0, 1, 2, 3, 4, 5, 6, 7}, 2);

  // One record across two openings, then a tampered opening that leaves the record as it was.
  {
    const OracleTreeShape s = [] {
      OracleTreeShape x;
      x.log_n = 2;
      x.log_n_zk = 2;
      x.main_symbols = {1};
      x.mask_symbols = {1};
      x.tree_number = 3;
      x.salt_bytes = 40;
      x.parameters = make_digest(20);
      x.run = make_digest(21);
      return x;
    }();
    const unsigned n = 4;
    std::vector<F> cols(n * s.width());
    std::vector<u8> salts(n * s.salt_bytes);
    std::vector<Digest> leaves(n);
    for (u64 pos = 0; pos < n; pos++) {
      for (size_t j = 0; j < s.width(); j++) cols[pos * s.width() + j] = col_f(pos, j);
      for (size_t k = 0; k < s.salt_bytes; k++) salts[pos * s.salt_bytes + k] = salt_byte(pos, k);
      leaves[pos] = oracle_leaf(s, pos, cols.data() + pos * s.width(), s.width(), salts.data() + pos * s.salt_bytes);
    }
    const TreeShape shape = s.tree();
    const Tag tag = shape.vertex_tag();
    std::map<u64, Digest> values;
    for (u64 pos = 0; pos < n; pos++) values[tree_index(s.log_n, pos)] = leaves[pos];
    for (unsigned d = s.log_n; d > 0; d--)
      for (u64 p = 0; p < ((u64)1 << (d - 1)); p++)
        values[tree_index(d - 1, p)] = vertex(tag, values[tree_index(d, 2 * p)], values[tree_index(d, 2 * p + 1)]);
    const Digest root = values[tree_index(0, 0)];
    std::printf("TREE3 log_n=%u log_n_zk=%u main=%zu mask=%zu tree_number=%u salt_bytes=%zu width=%zu ",
                s.log_n, s.log_n_zk, (size_t)s.main_width(), (size_t)s.mask_width(), s.tree_number, s.salt_bytes,
                s.width());
    pd("run", s.run);
    pd(" params", s.parameters);
    pd(" root", root);
    std::printf(" given=0 opening_bytes=0\n");
    for (u64 pos = 0; pos < n; pos++) {
      std::printf("COLS3 pos=%llu f=", (unsigned long long)pos);
      for (size_t j = 0; j < s.width(); j++)
        std::printf("%s%016llx", j ? "," : "", (unsigned long long)cols[pos * s.width() + j].v);
      std::printf(" salt=");
      phex(std::vector<u8>(salts.begin() + pos * s.salt_bytes, salts.begin() + (pos + 1) * s.salt_bytes));
      pd(" leaf", leaves[pos]);
      std::printf("\n");
    }
    TreeValues seen;
    for (int li = 0; li < 2; li++) {
      const std::vector<u64> draws = li == 0 ? std::vector<u64>{0, 2} : std::vector<u64>{1, 3};
      const PositionList list = PositionList::from_draws(draws, s.log_n);
      std::vector<Digest> given;
      Side side{shape, tag, list, leaves, given, values};
      Digest walked{};
      tree_walk(shape, list, side, walked);
      Opening o;
      o.main_width = s.main_width();
      o.mask_width = s.mask_width();
      for (size_t i = 0; i < list.size(); i++) {
        const u64 pos = list[i];
        for (size_t j = 0; j < s.width(); j++) o.columns.push_back(cols[pos * s.width() + j]);
        o.salts.insert(o.salts.end(), salts.begin() + pos * s.salt_bytes, salts.begin() + (pos + 1) * s.salt_bytes);
      }
      o.given = given;
      Writer w;
      write_opening(w, s, list, o);
      std::printf("LIST3 i=%d log_n=%u draws=", li, list.log_n());
      for (size_t i = 0; i < list.draws().size(); i++)
        std::printf("%s%llu", i ? "," : "", (unsigned long long)list.draws()[i]);
      std::printf(" led=1");
      pd(" walked", walked);
      std::printf(" given=%zu gn=%zu read=1 at_end=1 check=1 clash=0 vertices=0 entered=0\n", o.given.size(),
                  opening_given(s, list));
      std::printf("OPENING3 i=%d ", li);
      phex(w.bytes());
      std::printf("\n");
      bool clash = false;
      const bool ok = check_opening(root, s, list, o, &seen, &clash);
      std::printf("RECORD i=%d ok=%d clash=%d vertices=%zu entered=%llu\n", li, (int)ok, (int)clash, seen.vertices(),
                  (unsigned long long)seen.entered());
      if (li == 1) {
        o.columns[0].v ^= 1;
        const bool bad = check_opening(root, s, list, o, &seen, &clash);
        std::printf("RECORD_TAMPER ok=%d clash=%d vertices=%zu entered=%llu\n", (int)bad, (int)clash,
                    seen.vertices(), (unsigned long long)seen.entered());
      }
    }
  }

  // Codes: points, factors, generator rows, symbols, Encoder over F and E, the transform table,
  // short positions.
  {
    const Code codes[] = {{5, 3, 2}, {4, 8, 4}, {6, 5, 3}};
    for (int ci = 0; ci < 3; ci++) {
      const Code c = codes[ci];
      std::printf("CODE i=%d log_n=%u ell=%zu r=%zu ok=%d\n", ci, c.log_n, c.ell, c.r, (int)code_ok(c));
      const u64 n = c.n();
      const u64 positions[] = {0, 1, 3, n - 1};
      std::vector<F> message(c.ell), tail(c.r);
      std::vector<E> message_e(c.ell), tail_e(c.r);
      for (size_t j = 0; j < c.ell; j++) message[j] = F{100 + j};
      for (size_t j = 0; j < c.r; j++) tail[j] = F{200 + j};
      for (size_t j = 0; j < c.ell; j++) message_e[j] = E{{F{300 + j}, F{400 + j}, F{500 + j}}};
      for (size_t j = 0; j < c.r; j++) tail_e[j] = E{{F{600 + j}, F{700 + j}, F{800 + j}}};
      for (int pi = 0; pi < 4; pi++) {
        const u64 x = positions[pi];
        F f[64];
        factors(c, x, c.log_dim(), f);
        F mr[64], tr[64];
        for (int j = 0; j < 64; j++) mr[j] = tr[j] = F::zero();
        generator_row(c, x, mr, tr);
        const F sym = symbol_at(c, x, message.data(), tail.data());
        const E syme = symbol_at(c, x, message_e.data(), tail_e.data());
        std::printf("AT i=%d pos=%llu z=", ci, (unsigned long long)x);
        pf(F{gl64_point(c.log_n, x)});
        std::printf(" f=");
        for (unsigned j = 0; j < c.log_dim(); j++) std::printf("%s%016llx", j ? "," : "", (unsigned long long)f[j].v);
        std::printf(" ms=");
        pf(message_scale(c, f));
        std::printf(" ts=");
        pf(tail_scale(c, f));
        std::printf(" mrow=");
        for (size_t j = 0; j < c.ell; j++) std::printf("%s%016llx", j ? "," : "", (unsigned long long)mr[j].v);
        std::printf(" trow=");
        for (size_t j = 0; j < c.r; j++) std::printf("%s%016llx", j ? "," : "", (unsigned long long)tr[j].v);
        std::printf(" symf=");
        pf(sym);
        std::printf(" syme=");
        pv(syme);
        std::printf("\n");
      }
      Encoder enc(c);
      std::vector<F> word(n), m2(c.ell), t2(c.r);
      enc.encode(message.data(), tail.data(), word.data());
      const bool decoded = enc.decode(word.data(), m2.data(), t2.data());
      std::printf("ENC_F i=%d word=", ci);
      for (u64 j = 0; j < n; j++) std::printf("%s%016llx", j ? "," : "", (unsigned long long)word[j].v);
      std::printf(" decode=%d\n", (int)decoded);
      std::vector<E> worde(n), me2(c.ell), te2(c.r);
      enc.encode(message_e.data(), tail_e.data(), worde.data());
      const bool decoded_e = enc.decode(worde.data(), me2.data(), te2.data());
      std::printf("ENC_E i=%d word=", ci);
      for (u64 j = 0; j < n; j++) {
        if (j) std::printf(";");
        pv(worde[j]);
      }
      std::printf(" decode=%d\n", (int)decoded_e);
      std::vector<u64> tw;
      gl64_table(c.log_n, gl64_subgroup_log(c.log_n), tw);
      std::printf("TABLE i=%d v=", ci);
      for (size_t j = 0; j < tw.size(); j++) std::printf("%s%016llx", j ? "," : "", (unsigned long long)tw[j]);
      std::printf("\n");
    }
    const unsigned logs[] = {3, 5, 32, 40};
    const unsigned shorts[] = {0, 2, 4};
    int si = 0;
    for (unsigned ln : logs)
      for (unsigned ls : shorts) {
        if (ls > ln) continue;
        for (u64 x : {(u64)0, (u64)1, (u64)6, (u64)((1ull << ln) - 1)}) {
          std::printf("SHORT i=%d log_n=%u log_short=%u x=%llu v=%llu\n", si++, ln, ls, (unsigned long long)x,
                      (unsigned long long)short_position(ln, ls, x));
        }
      }
  }
  return 0;
}
