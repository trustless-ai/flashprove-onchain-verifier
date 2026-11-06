// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for the verifier-reachable part of LKP (`blocks/iop/lkp.h`): the public data and its
// bytes and faults, the cubes, the rows and the table's extension, the orders, the summands, the
// mask counts, the claim on the keys, the live blocks, the weights of one block and the honest
// multiplicities. The prover's engine (`LkpCpu`, `LkpProver`), its coins and the rounds that need a
// channel are not used: the claim on the keys is the block at the end of lkp_run(), written out
// here as the C++ has it.
//
// Build with -DBLK_FIELD=2.

#include "iop/lkp.h"

#include <cstdio>
#include <string>
#include <utility>
#include <vector>

using namespace blk;

namespace {

E mk(u64 x) { return E::from(F{x}, F{x + 1}, F{x + 2}); }
std::vector<E> mkvec(size_t n, u64 base) {
  std::vector<E> v;
  for (size_t i = 0; i < n; i++) v.push_back(mk(base + i));
  return v;
}

std::string e_str(const E &x) {
  char b[80];
  std::snprintf(b, sizeof b, "%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v,
                (unsigned long long)x.c[1].v, (unsigned long long)x.c[2].v);
  return b;
}
std::string es_str(const std::vector<E> &v) {
  if (v.empty()) return "-";
  std::string s;
  for (size_t i = 0; i < v.size(); i++) s += (i ? ";" : "") + e_str(v[i]);
  return s;
}
std::string us_str(const std::vector<unsigned> &v) {
  if (v.empty()) return "-";
  std::string s;
  for (size_t i = 0; i < v.size(); i++) s += (i ? "," : "") + std::to_string(v[i]);
  return s;
}
std::string fault_str(const char *f) {
  std::string s = f ? f : "-";
  for (char &c : s)
    if (c == ' ') c = '_';
  return s;
}
std::string bytes_str(const std::vector<u8> &b) {
  static const char *h = "0123456789abcdef";
  std::string s;
  for (u8 x : b) s += h[x >> 4], s += h[x & 15];
  return s;
}
std::string kbs_str(const std::vector<LkpKeyBlock> &v) {
  if (v.empty()) return "-";
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    const LkpKeyBlock &b = v[i];
    s += (i ? ";" : "") + std::to_string(b.first) + ":" + std::to_string(b.log_trees) + ":" +
         std::to_string(b.function) + ":" + std::to_string(b.padding_row);
  }
  return s;
}
std::string tps_str(const std::vector<LkpTablePart> &v) {
  if (v.empty()) return "-";
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    const LkpTablePart &t = v[i];
    s += (i ? "|" : "") + std::to_string(t.first) + ":" + std::to_string(t.log_rows) + ":" +
         std::to_string(t.function) + ":" + es_str(t.rows);
  }
  return s;
}
std::string pads_str(const std::vector<LkpPadding> &v) {
  if (v.empty()) return "-";
  std::string s;
  for (size_t i = 0; i < v.size(); i++) {
    const LkpPadding &p = v[i];
    s += (i ? ";" : "") + std::to_string(p.part) + ":" + std::to_string(p.first) + ":" +
         std::to_string(p.log_step) + ":" + std::to_string(p.length) + ":" + std::to_string(p.row);
  }
  return s;
}
std::string cube_str(const LkpCube &c) { return std::to_string(c.mask) + ":" + std::to_string(c.value); }
std::string cubes_str(const std::vector<LkpCube> &v) {
  if (v.empty()) return "-";
  std::string s;
  for (size_t i = 0; i < v.size(); i++) s += (i ? ";" : "") + cube_str(v[i]);
  return s;
}
std::string blocks_str(const std::vector<std::pair<unsigned, unsigned>> &v) {
  if (v.empty()) return "-";
  std::string s;
  for (size_t i = 0; i < v.size(); i++)
    s += (i ? ";" : "") + std::to_string(v[i].first) + ":" + std::to_string(v[i].second);
  return s;
}

LkpPadding pad(unsigned part, u64 first, unsigned log_step, u64 length, u64 row) {
  LkpPadding p;
  p.part = part, p.first = first, p.log_step = log_step, p.length = length, p.row = row;
  return p;
}
LkpKeyBlock kb(u64 first, unsigned log_trees, int function, u64 padding_row) {
  LkpKeyBlock b;
  b.first = first, b.log_trees = log_trees, b.function = function, b.padding_row = padding_row;
  return b;
}
LkpTablePart tp(u64 first, unsigned log_rows, unsigned function, std::vector<E> rows) {
  LkpTablePart t;
  t.first = first, t.log_rows = log_rows, t.function = function, t.rows = std::move(rows);
  return t;
}
LkpPublic mk_public(std::vector<unsigned> parts, unsigned d, unsigned mu, unsigned live, unsigned h,
                    unsigned g, bool shifted, std::vector<OracleId> read_from,
                    std::vector<LkpKeyBlock> keys, std::vector<LkpTablePart> tables,
                    std::vector<LkpPadding> padding, std::vector<unsigned> order) {
  LkpPublic S;
  S.parts = std::move(parts), S.d = d, S.mu = mu, S.live = live, S.h = h, S.g = g;
  S.shifted = shifted, S.read_from = std::move(read_from), S.keys = std::move(keys);
  S.tables = std::move(tables), S.padding = std::move(padding);
  S.last_key_level_order = std::move(order);
  return S;
}

void print_public(const char *name, const LkpPublic &S) {
  Writer w;
  public_bytes(w, S);
  std::printf(
      "LKP_PUBLIC name=%s parts=%s d=%u mu=%u live=%u h=%u g=%u shifted=%u read_from=%s keys=%s "
      "tables=%s padding=%s order=%s planes=%u all_keys=%llu bytes=%s fault=%s\n",
      name, us_str(S.parts).c_str(), S.d, S.mu, S.live, S.h, S.g, (unsigned)S.shifted,
      us_str(S.read_from).c_str(), kbs_str(S.keys).c_str(), tps_str(S.tables).c_str(),
      pads_str(S.padding).c_str(), us_str(S.last_key_level_order).c_str(), S.planes(),
      (unsigned long long)S.all_keys(), bytes_str(w.bytes()).c_str(), fault_str(lkp_fault(S)).c_str());
}

// The block at the end of lkp_run(): one part's claim on its leaves becomes the claim on its keys.
LkpKeys key_claim(const LkpPublic &fixed, const E &theta, const E &alpha, unsigned part,
                  PointClaim<E> on_leaves) {
  LkpKeys k;
  k.point = std::move(on_leaves.point);
  for (MaskTerm<E> &m : on_leaves.masks) k.masks.push_back({std::move(m.slot), -m.coeff});
  k.target = alpha - on_leaves.value;
  k.weights.add(Tensor::eq(k.point.data(), (unsigned)k.point.size()));
  auto take_out = [&](const LkpCube &cube, u64 row) {
    const E weight = lkp_cube_weight(cube, k.point);
    k.target = k.target - weight * lkp_row(fixed, theta, row);
    k.weights.add(lkp_cube_tensor(cube, k.point, -E::one()));
    return weight;
  };
  std::vector<E> real(fixed.keys.size(), E::zero());
  for (size_t b = 0; b < fixed.keys.size(); b++) {
    if (fixed.keys[b].function < 0)
      take_out(lkp_cube(fixed, fixed.keys[b]), fixed.keys[b].padding_row);
    else
      real[b] = lkp_cube_weight(lkp_cube(fixed, fixed.keys[b]), k.point);
  }
  for (const LkpPadding &p : fixed.padding) {
    if (p.part != part) continue;
    const size_t b = size_t(&lkp_block_of(fixed, p.first) - fixed.keys.data());
    for (const LkpCube &cube : lkp_cubes(p, (unsigned)k.point.size()))
      real[b] = real[b] - take_out(cube, p.row);
  }
  for (size_t b = 0; b < fixed.keys.size(); b++)
    if (fixed.keys[b].function > 0)
      k.target = k.target - theta * E::from(from_u64((u64)fixed.keys[b].function)) * real[b];
  return k;
}

void print_key_claim(const char *name, const LkpPublic &S, unsigned part, const E &theta,
                     const E &alpha, const std::vector<E> &point, const E &value) {
  PointClaim<E> leaves;
  leaves.point = point, leaves.value = value;
  const LkpKeys k = key_claim(S, theta, alpha, part, std::move(leaves));
  std::vector<E> wat;
  for (u64 j = 0; j < (u64(1) << k.point.size()); j++) wat.push_back(k.weights.at(j));
  std::printf(
      "LKP_KEY_CLAIM public=%s part=%u theta=%s alpha=%s point=%s value=%s target=%s wvars=%zu "
      "wcount=%zu masks=%zu wat=%s\n",
      name, part, e_str(theta).c_str(), e_str(alpha).c_str(), es_str(k.point).c_str(),
      e_str(value).c_str(), e_str(k.target).c_str(), k.point.size(), k.weights.tensors.size(),
      k.masks.size(), es_str(wat).c_str());
}

// LKP's weights on one part's keys, from the definitions (as the C++ test builds them): the
// equality vector less one product form per padding cube, of a padding-only block and of a run.
Form weights_on_keys(const LkpPublic &S, unsigned part, const std::vector<E> &point) {
  Form f;
  f.add(Tensor::eq(point.data(), S.part_bits()[0]));
  for (const LkpKeyBlock &b : S.keys)
    if (b.function < 0) f.add(lkp_cube_tensor(lkp_cube(S, b), point, -E::one()));
  for (const LkpPadding &p : S.padding) {
    if (p.part != part) continue;
    for (const LkpCube &c : lkp_cubes(p, S.part_bits()[0]))
      f.add(lkp_cube_tensor(c, point, -E::one()));
  }
  return f;
}

void print_weights_of_block(const LkpPublic &S, const char *name, unsigned part, size_t block,
                            const std::vector<E> &point) {
  const Form all = weights_on_keys(S, part, point);
  const Form own = lkp_weights_of_block(S, all, block);
  std::vector<E> at;
  for (u64 j = 0; j < (u64(1) << S.part_bits()[0]); j++) at.push_back(own.at(j));
  std::printf("LKP_WEIGHTS_OF_BLOCK public=%s part=%u block=%zu point=%s wvars=%u wcount=%zu at=%s\n",
              name, part, block, es_str(point).c_str(), S.part_bits()[0], own.tensors.size(),
              es_str(at).c_str());
}

}  // namespace

int main() {
  std::setvbuf(stdout, nullptr, _IONBF, 0);
  const std::vector<OracleId> read_from0 = {0};

  // A range table of 8 rows, one part of 8 keys, g = 0.
  const LkpPublic range = mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                                    {tp(0, 3, 0, {})}, {}, {});
  // The same with trees: g = 2, one block of all four trees.
  const LkpPublic range_g = mk_public({4}, 3, 4, 6, 0, 2, false, read_from0, {kb(0, 2, 0, 0)},
                                      {tp(0, 3, 0, {})}, {}, {});
  // A written-out table in two parts.
  const LkpPublic written = mk_public(
      {3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
      {tp(0, 2, 0, {mk(100), mk(101), mk(102), mk(103)}),
       tp(4, 2, 0, {mk(104), mk(105), mk(106), mk(107)})},
      {}, {});
  // The table parts numbered in the low h bits of the row.
  const LkpPublic hparts = mk_public(
      {4}, 3, 4, 6, 1, 2, false, read_from0, {kb(0, 2, 0, 0)},
      {tp(0, 1, 0, {mk(200), mk(201)}), tp(1, 1, 0, {mk(202), mk(203)})}, {}, {});
  // Two functions under one shift; a run of padding in function 0's tree.
  const LkpPublic shifted =
      mk_public({3}, 3, 4, 6, 0, 1, true, read_from0, {kb(0, 0, 0, 0), kb(1, 0, 1, 0)},
                {tp(0, 3, 0, {})}, {pad(0, 2, 1, 1, 1)}, {});
  // Two runs of padding in a range table.
  const LkpPublic padding = mk_public({3}, 2, 3, 6, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                                      {tp(0, 2, 0, {})}, {pad(0, 1, 0, 2, 1)}, {});
  // A padding-only block of trees next to a function's block.
  const LkpPublic padding_tree =
      mk_public({3}, 2, 3, 6, 0, 1, false, read_from0, {kb(0, 0, -1, 1), kb(1, 0, 0, 0)},
                {tp(0, 2, 0, {})}, {pad(0, 3, 1, 1, 0)}, {});
  // Two parts of keys, under one tree.
  const LkpPublic multipart = mk_public({2, 3}, 3, 4, 7, 0, 0, false, read_from0,
                                        {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {});
  // An order of the last key level's variables.
  const LkpPublic order_pub = mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                                        {tp(0, 3, 0, {})}, {}, {1, 0});
  // A run whose cubes are not one: 1 + 2 * {0, 1, 2, 3, 4} in a part of 16 keys.
  const LkpPublic cubes = mk_public({4}, 3, 4, 7, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                                    {tp(0, 3, 0, {})}, {pad(0, 1, 1, 5, 2)}, {});
  // A tiny table for the multiplicities.
  const LkpPublic count_pub = mk_public({2}, 2, 3, 3, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                                        {tp(0, 2, 0, {})}, {}, {});
  // All plane slots live.
  const LkpPublic live_zero = mk_public({3}, 3, 3, 0, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                                        {tp(0, 3, 0, {})}, {}, {});

  const std::vector<std::pair<std::string, LkpPublic>> valid = {
      {"range", range},         {"range_g", range_g}, {"written", written},
      {"hparts", hparts},       {"shifted", shifted}, {"padding", padding},
      {"padding_tree", padding_tree}, {"multipart", multipart},
      {"order", order_pub},     {"cubes", cubes},     {"count", count_pub},
      {"live_zero", live_zero},
  };
  for (const auto &[name, S] : valid) print_public(name.c_str(), S);

  // The faults, one for each check of lkp_fault().
  const std::vector<std::pair<std::string, LkpPublic>> bad = {
      {"empty_read",
       mk_public({3}, 3, 3, 5, 0, 0, false, {}, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"empty_parts",
       mk_public({}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"mu_zero",
       mk_public({3}, 3, 0, 0, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"mu_seven",
       mk_public({3}, 3, 7, 0, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"live_all",
       mk_public({3}, 3, 3, 8, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"live_one",
       mk_public({3}, 3, 3, 1, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"part_zero",
       mk_public({0}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"part_too_many",
       mk_public({5}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"keys_wrap",
       mk_public({2, 2, 3}, 3, 3, 4, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"d_too_big",
       mk_public({3}, 64, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 64, 0, {})}, {}, {})},
      {"d_planes_wrap",
       mk_public({3}, 58, 6, 6, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 58, 0, {})}, {}, {})},
      {"multipart_shift",
       mk_public({2, 3}, 3, 4, 7, 0, 1, true, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"multipart_g",
       mk_public({2, 3}, 3, 4, 7, 0, 1, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"g_too_big",
       mk_public({2}, 3, 4, 7, 0, 3, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"key_block_unaligned",
       mk_public({4}, 3, 4, 7, 0, 2, false, read_from0, {kb(1, 2, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"key_blocks_overlap",
       mk_public({4}, 3, 4, 7, 0, 2, false, read_from0, {kb(0, 2, 0, 0), kb(2, 1, 0, 0)},
                 {tp(0, 3, 0, {})}, {}, {})},
      {"trees_not_cover",
       mk_public({4}, 3, 4, 7, 0, 2, false, read_from0, {kb(0, 1, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"padding_row_block",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, -1, 8)}, {tp(0, 3, 0, {})}, {}, {})},
      {"unshifted_key_function",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 1, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"unshifted_table_function",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 1, {})}, {}, {})},
      {"h_too_big",
       mk_public({3}, 3, 3, 5, 4, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"h_numbering",
       mk_public({3}, 3, 3, 5, 1, 0, false, read_from0, {kb(0, 0, 0, 0)},
                 {tp(1, 2, 0, {}), tp(0, 3, 0, {})}, {}, {})},
      {"written_rows",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                 {tp(0, 2, 0, {mk(1), mk(2), mk(3)})}, {}, {})},
      {"tables_not_cover",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 2, 0, {})}, {}, {})},
      {"padding_part",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                 {pad(1, 0, 0, 1, 0)}, {})},
      {"padding_empty",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                 {pad(0, 0, 0, 0, 0)}, {})},
      {"padding_outside",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                 {pad(0, 6, 0, 3, 0)}, {})},
      {"padding_leaves_tree",
       mk_public({4}, 3, 4, 7, 0, 2, false, read_from0, {kb(0, 2, 0, 0)}, {tp(0, 3, 0, {})},
                 {pad(0, 1, 1, 1, 0)}, {})},
      {"padding_in_padding_tree",
       mk_public({3}, 3, 3, 5, 0, 1, false, read_from0, {kb(0, 0, -1, 0), kb(1, 0, 0, 0)},
                 {tp(0, 3, 0, {})}, {pad(0, 0, 1, 1, 0)}, {})},
      {"padding_order",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                 {pad(0, 4, 0, 1, 0), pad(0, 1, 0, 1, 0)}, {})},
      {"padding_meet",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                 {pad(0, 0, 0, 2, 0), pad(0, 1, 0, 2, 0)}, {})},
      {"only_padding_all",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, -1, 0)}, {tp(0, 3, 0, {})}, {}, {})},
      {"only_padding_part",
       mk_public({2, 3}, 3, 4, 7, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                 {pad(0, 0, 0, 4, 0)}, {})},
      {"order_dup",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                 {1, 1})},
      {"order_out",
       mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                 {2})},
  };
  for (const auto &[name, S] : bad) print_public(name.c_str(), S);

  // The faults again, one mutation of a valid lookup for each check of lkp_fault() (plus the two
  // lawful multi-block/multi-table layouts that the overlap checks must not reject). Each line
  // carries the whole mutated lookup, so a reader can replay lkp_fault() exactly; `fault=-` means
  // that it accepted the lookup.
  auto fault_case = [](const char *name, const LkpPublic &S) {
    std::printf(
        "LKP_FAULT name=%s parts=%s d=%u mu=%u live=%u h=%u g=%u shifted=%u read_from=%s keys=%s "
        "tables=%s padding=%s order=%s fault=%s\n",
        name, us_str(S.parts).c_str(), S.d, S.mu, S.live, S.h, S.g, (unsigned)S.shifted,
        us_str(S.read_from).c_str(), kbs_str(S.keys).c_str(), tps_str(S.tables).c_str(),
        pads_str(S.padding).c_str(), us_str(S.last_key_level_order).c_str(),
        fault_str(lkp_fault(S)).c_str());
  };
  LkpPublic many_padding = range;
  many_padding.padding.assign(4097, pad(0, 0, 0, 1, 0));
  fault_case("ok_range", range);
  // The two lawful layouts of the RNG vectors: several key blocks and table parts tile the tree
  // numbers and the rows, and (b) two runs of padding sit in one part, so lkp_fault() accepts them.
  fault_case("ok_rng_a",
             mk_public({3}, 2, 2, 0, 0, 1, true, {3, 4}, {kb(0, 0, 0, 0), kb(1, 0, 1, 0)},
                       {tp(0, 1, 0, {}), tp(2, 1, 1, {})}, {}, {}));
  fault_case("ok_rng_b",
             mk_public({4}, 2, 3, 5, 0, 1, true, {3, 4}, {kb(0, 0, 0, 0), kb(1, 0, 1, 0)},
                       {tp(0, 1, 0, {}), tp(2, 1, 1, {})},
                       {pad(0, 12, 1, 2, 0), pad(0, 13, 1, 2, 2)}, {}));
  fault_case("empty_read",
             mk_public({3}, 3, 3, 5, 0, 0, false, {}, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {}, {}));
  fault_case("empty_parts",
             mk_public({}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("mu_zero",
             mk_public({3}, 3, 0, 0, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("mu_seven",
             mk_public({3}, 3, 7, 0, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("live_all",
             mk_public({3}, 3, 3, 8, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("live_one",
             mk_public({3}, 3, 3, 1, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("planes_64",
             mk_public({3}, 3, 6, 0, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("part_zero",
             mk_public({0}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("part_too_many",
             mk_public({5}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("parts_too_many_bits",
             mk_public({4, 4}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                       {tp(0, 3, 0, {})}, {}, {}));
  fault_case("keys_wrap",
             mk_public({2, 2, 3}, 3, 3, 4, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                       {tp(0, 3, 0, {})}, {}, {}));
  fault_case("d_too_big",
             mk_public({3}, 64, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 64, 0, {})},
                       {}, {}));
  fault_case("d_planes_wrap",
             mk_public({3}, 58, 6, 6, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 58, 0, {})},
                       {}, {}));
  fault_case("multipart_shift",
             mk_public({2, 3}, 3, 4, 7, 0, 0, true, read_from0, {kb(0, 0, 0, 0)},
                       {tp(0, 3, 0, {})}, {}, {}));
  fault_case("multipart_g",
             mk_public({2, 3}, 3, 4, 7, 0, 1, false, read_from0, {kb(0, 0, 0, 0)},
                       {tp(0, 3, 0, {})}, {}, {}));
  fault_case("g_too_big",
             mk_public({2}, 3, 4, 7, 0, 3, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("key_block_unaligned",
             mk_public({4}, 3, 4, 7, 0, 2, false, read_from0, {kb(1, 2, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("key_blocks_overlap",
             mk_public({4}, 3, 4, 7, 0, 2, false, read_from0, {kb(0, 2, 0, 0), kb(2, 1, 0, 0)},
                       {tp(0, 3, 0, {})}, {}, {}));
  fault_case("trees_not_cover",
             mk_public({4}, 3, 4, 7, 0, 2, false, read_from0, {kb(0, 1, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("unshifted_key_function",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 1, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("unshifted_table_function",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 1, {})}, {},
                       {}));
  fault_case("h_too_big",
             mk_public({3}, 3, 3, 5, 4, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {}));
  fault_case("h_numbering",
             mk_public({3}, 3, 3, 5, 1, 0, false, read_from0, {kb(0, 0, 0, 0)},
                       {tp(1, 2, 0, {})}, {}, {}));
  fault_case("written_rows",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                       {tp(0, 2, 0, {mk(1), mk(2), mk(3)})}, {}, {}));
  // The same check on the h != 0 branch, where the tables are numbered by their low bits.
  fault_case("written_rows_h",
             mk_public({4}, 3, 4, 6, 1, 2, false, read_from0, {kb(0, 2, 0, 0)},
                       {tp(0, 1, 0, {mk(1), mk(2), mk(3)}), tp(1, 1, 0, {})}, {}, {}));
  fault_case("table_unaligned",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(1, 1, 0, {})},
                       {}, {}));
  fault_case("table_overlap",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                       {tp(0, 2, 0, {}), tp(0, 2, 0, {})}, {}, {}));
  fault_case("tables_not_cover",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 2, 0, {})}, {},
                       {}));
  fault_case("padding_over_4096", many_padding);
  fault_case("padding_part",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                       {pad(1, 0, 0, 1, 0)}, {}));
  fault_case("padding_empty",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                       {pad(0, 0, 0, 0, 0)}, {}));
  fault_case("padding_outside",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                       {pad(0, 6, 0, 3, 0)}, {}));
  fault_case("padding_row",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                       {pad(0, 0, 0, 1, 8)}, {}));
  fault_case("padding_leaves_tree",
             mk_public({3}, 3, 4, 6, 0, 1, false, read_from0, {kb(0, 1, 0, 0)}, {tp(0, 3, 0, {})},
                       {pad(0, 0, 0, 1, 0)}, {}));
  fault_case("padding_in_padding_tree",
             mk_public({3}, 3, 3, 5, 0, 1, false, read_from0, {kb(0, 0, -1, 0), kb(1, 0, 0, 0)},
                       {tp(0, 3, 0, {})}, {pad(0, 0, 1, 1, 0)}, {}));
  fault_case("padding_order",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                       {pad(0, 4, 0, 1, 0), pad(0, 1, 0, 1, 0)}, {}));
  fault_case("padding_meet",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})},
                       {pad(0, 0, 0, 2, 0), pad(0, 1, 0, 2, 0)}, {}));
  fault_case("only_padding_all",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, -1, 0)}, {tp(0, 3, 0, {})},
                       {}, {}));
  fault_case("only_padding_part",
             mk_public({2, 3}, 3, 4, 7, 0, 0, false, read_from0, {kb(0, 0, 0, 0)},
                       {tp(0, 3, 0, {})}, {pad(0, 0, 0, 4, 0)}, {}));
  fault_case("only_padding_tree",
             mk_public({3}, 3, 3, 5, 0, 1, false, read_from0, {kb(0, 0, 0, 0), kb(1, 0, -1, 0)},
                       {tp(0, 3, 0, {})}, {pad(0, 0, 1, 4, 0)}, {}));
  fault_case("order_dup",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {1, 1}));
  fault_case("order_out",
             mk_public({3}, 3, 3, 5, 0, 0, false, read_from0, {kb(0, 0, 0, 0)}, {tp(0, 3, 0, {})}, {},
                       {2}));

  const E theta = mk(11);
  const E alpha = mk(5);
  for (const auto &[name, S] : valid) {
    const std::vector<E> point_d = mkvec(S.d, 30);
    std::printf("LKP_ROWS public=%s theta=%s rows=%s\n", name.c_str(), e_str(theta).c_str(),
                es_str(lkp_rows(S, theta)).c_str());
    std::printf("LKP_TABLE_AT public=%s theta=%s point=%s out=%s\n", name.c_str(),
                e_str(theta).c_str(), es_str(point_d).c_str(),
                e_str(lkp_table_at(S, theta, point_d)).c_str());
    std::printf("LKP_PADDING public=%s count=%llu only=%d\n", name.c_str(),
                (unsigned long long)lkp_padding_count(S), (int)lkp_only_padding(S));
    std::printf("LKP_MASKS public=%s key_masks=%zu masks=%zu\n", name.c_str(), lkp_key_masks(S),
                lkp_masks(S));
    for (size_t part = 0; part < S.parts.size(); part++)
      for (u64 i = 0; i < 8 && i < (u64(1) << S.parts[part]); i++)
        std::printf("LKP_IS_PADDING public=%s part=%zu i=%llu value=%d\n", name.c_str(), part,
                    (unsigned long long)i, (int)lkp_is_padding(S, (unsigned)part, i));
    for (u64 t = 0; t < (u64(1) << S.d); t++)
      std::printf("LKP_ROW public=%s theta=%s t=%llu value=%s\n", name.c_str(), e_str(theta).c_str(),
                  (unsigned long long)t, e_str(lkp_row(S, theta, t)).c_str());
    for (u64 y = 0; y < (u64(1) << S.g); y++) {
      const LkpKeyBlock &b = lkp_block_of(S, y);
      std::printf("LKP_BLOCK public=%s key=%llu first=%llu log_trees=%u function=%d padding_row=%llu\n",
                  name.c_str(), (unsigned long long)y, (unsigned long long)b.first, b.log_trees,
                  b.function, (unsigned long long)b.padding_row);
    }
    {
      const LkpShape shape = lkp_shape(S, theta);
      std::string ps;
      for (size_t i = 0; i < shape.padding.size(); i++)
        ps += (i ? ";" : "") + std::to_string(shape.padding[i].first) + ":" +
              e_str(shape.padding[i].second);
      std::printf(
          "LKP_SHAPE public=%s theta=%s d=%u mu=%u planes=%u part_bits=%s all_keys=%llu order=%s "
          "pad=%s point=%s table_at=%s\n",
          name.c_str(), e_str(theta).c_str(), shape.d, shape.mu, shape.planes,
          us_str(shape.part_bits).c_str(), (unsigned long long)shape.all_keys,
          us_str(shape.last_key_level_order).c_str(), ps.empty() ? "-" : ps.c_str(),
          es_str(point_d).c_str(), e_str(shape.table_at(point_d)).c_str());
    }
  }

  // The claim on the keys, for a few publics and parts.
  for (const auto &[name, S] : valid) {
    if (S.d + S.mu > 7) continue;
    const std::vector<E> point = mkvec(S.mu + S.d, 40);
    for (unsigned part = 0; part < S.parts.size(); part++)
      print_key_claim(name.c_str(), S, part, theta, alpha, point, mk(99));
  }
  print_weights_of_block(range_g, "range_g", 0, 0, mkvec(range_g.part_bits()[0], 40));
  print_weights_of_block(shifted, "shifted", 0, 0, mkvec(shifted.part_bits()[0], 40));
  print_weights_of_block(shifted, "shifted", 0, 1, mkvec(shifted.part_bits()[0], 40));
  print_weights_of_block(hparts, "hparts", 0, 0, mkvec(hparts.part_bits()[0], 40));
  print_weights_of_block(padding_tree, "padding_tree", 0, 1,
                         mkvec(padding_tree.part_bits()[0], 40));
  print_weights_of_block(cubes, "cubes", 0, 0, mkvec(cubes.part_bits()[0], 40));
  print_weights_of_block(multipart, "multipart", 0, 0, mkvec(multipart.part_bits()[0], 40));

  // Cubes and their weights.
  const std::vector<LkpPadding> runs = {pad(0, 1, 1, 5, 0), pad(0, 5, 0, 6, 0), pad(0, 0, 2, 3, 0)};
  const std::vector<E> z = mkvec(4, 70);
  for (const LkpPadding &p : runs) {
    const std::vector<LkpCube> cs = lkp_cubes(p, 4);
    std::printf("LKP_CUBES first=%llu log_step=%u length=%llu bits=4 cubes=%s\n",
                (unsigned long long)p.first, p.log_step, (unsigned long long)p.length,
                cubes_str(cs).c_str());
    for (const LkpCube &c : cs) {
      std::printf("LKP_CUBE_WEIGHT mask=%llu value=%llu z=%s out=%s\n",
                  (unsigned long long)c.mask, (unsigned long long)c.value, es_str(z).c_str(),
                  e_str(lkp_cube_weight(c, z)).c_str());
      const E scalar = mk(80);
      const Tensor t = lkp_cube_tensor(c, z, scalar);
      std::vector<E> at;
      for (u64 j = 0; j < 16; j++) at.push_back(t.at(j));
      std::printf("LKP_CUBE_TENSOR mask=%llu value=%llu z=%s scalar=%s vars=%u scalar_out=%s at=%s\n",
                  (unsigned long long)c.mask, (unsigned long long)c.value, es_str(z).c_str(),
                  e_str(scalar).c_str(), t.vars(), e_str(t.scalar).c_str(), es_str(at).c_str());
    }
  }

  // The orders.
  std::printf("LKP_ORDER kind=default variables=5 out=%s\n",
              us_str(lkp_default_order(5)).c_str());
  std::printf("LKP_ORDER kind=beginning variables=4 first=1,0 out=%s\n",
              us_str(lkp_order_beginning({1, 0}, 4)).c_str());
  std::printf("LKP_ORDER kind=range variables=12 g=2 out=%s\n",
              us_str(lkp_range_order(12, 2)).c_str());
  std::printf("LKP_ORDER kind=range variables=10 g=1 out=%s\n",
              us_str(lkp_range_order(10, 1)).c_str());
  {
    const std::vector<unsigned> order = lkp_default_order(3);
    const std::vector<E> table = mkvec(8, 90);
    std::printf("LKP_IN_ORDER order=%s table=%s out=%s\n", us_str(order).c_str(),
                es_str(table).c_str(), es_str(lkp_in_order(table, order)).c_str());
    std::printf("LKP_BY_VARIABLE order=%s by_round=%s out=%s\n", us_str(order).c_str(),
                es_str(table).c_str(), es_str(lkp_by_variable(table, order)).c_str());
    const std::vector<unsigned> order2 = lkp_range_order(12, 2);
    std::printf("LKP_IN_ORDER_12 order=%s out=%s\n", us_str(order2).c_str(),
                es_str(lkp_in_order(mkvec(1 << 12, 120), order2)).c_str());
    std::printf("LKP_BY_VARIABLE_12 order=%s out=%s\n", us_str(order2).c_str(),
                es_str(lkp_by_variable(mkvec(1 << 12, 130), order2)).c_str());
  }

  // The summands.
  {
    const std::vector<E> y2 = {mk(1), mk(2)};
    const std::vector<E> y3 = {mk(1), mk(2), mk(3)};
    const std::vector<E> y1 = {mk(1)};
    auto out_of = [](const Summand<E> &s, const std::vector<E> &y) {
      const std::vector<E> none;
      return es_str(s.at(none, y));
    };
    const Summand<E> prod = lkp_summand_product();
    std::printf("LKP_SUMMAND kind=product shown=%u kept=%u degree=%u y=%s out=%s\n", prod.shown,
                prod.kept, prod.degree, es_str(y2).c_str(), out_of(prod, y2).c_str());
    const Summand<E> tie0 = lkp_summand_tie(true, mk(7));
    std::printf("LKP_SUMMAND kind=tie_first shown=%u kept=%u degree=%u a=%s y=%s out=%s\n", tie0.shown,
                tie0.kept, tie0.degree, e_str(mk(7)).c_str(), es_str(y3).c_str(),
                out_of(tie0, y3).c_str());
    const Summand<E> tie1 = lkp_summand_tie(false, mk(7));
    std::printf("LKP_SUMMAND kind=tie shown=%u kept=%u degree=%u a=%s y=%s out=%s\n", tie1.shown,
                tie1.kept, tie1.degree, e_str(mk(7)).c_str(), es_str(y2).c_str(),
                out_of(tie1, y2).c_str());
    const Summand<E> bits = lkp_summand_bits();
    std::printf("LKP_SUMMAND kind=bits shown=%u kept=%u degree=%u y=%s out=%s\n", bits.shown,
                bits.kept, bits.degree, es_str(y1).c_str(), out_of(bits, y1).c_str());
    for (const auto &[name, S] : valid) {
      if (S.mu + S.d > 7) continue;
      const LkpShape shape = lkp_shape(S, theta);
      const std::vector<unsigned> ord = lkp_default_order(S.mu + S.d);
      const Summand<E> leaves = lkp_summand_leaves(shape, alpha, ord);
      // shown = 0: the point is the first argument, the (empty) shown values the second.
      const std::vector<E> by_round = mkvec(S.mu + S.d, 60);
      const std::vector<E> no_y;
      std::printf("LKP_SUMMAND kind=leaves public=%s theta=%s shown=%u kept=%u degree=%u alpha=%s "
                  "order=%s by_round=%s out=%s\n",
                  name.c_str(), e_str(theta).c_str(), leaves.shown, leaves.kept, leaves.degree,
                  e_str(alpha).c_str(), us_str(ord).c_str(), es_str(by_round).c_str(),
                  es_str(leaves.at(by_round, no_y)).c_str());
    }
  }

  // The multiplicities.
  {
    auto count_line = [&](const char *case_name, const char *public_name, const LkpPublic &S,
                          const std::vector<E> &keys, const std::vector<bool> &left_out) {
      std::vector<E> bits;
      const bool ok = lkp_count(S, keys, bits, left_out);
      std::string lfts;
      for (size_t i = 0; i < left_out.size(); i++)
        if (left_out[i]) lfts += (lfts.empty() ? "" : ",") + std::to_string(i);
      std::printf("LKP_COUNT case=%s public=%s keys=%s left=%s ok=%d bits=%s\n", case_name,
                  public_name, es_str(keys).c_str(), lfts.empty() ? "-" : lfts.c_str(), (int)ok,
                  es_str(bits).c_str());
    };
    std::vector<E> range_keys, count_keys;
    for (u64 i = 0; i < 8; i++) range_keys.push_back(E::from(from_u64(i)));
    for (u64 i = 0; i < 4; i++)
      count_keys.push_back(E::from(from_u64(i == 2 ? 1 : (i == 3 ? 2 : i))));
    count_line("range", "range", range, range_keys, {});
    count_line("count", "count", count_pub, count_keys, {});
    count_line("padding", "padding", padding, range_keys, {});
    count_line("padding_tree", "padding_tree", padding_tree, range_keys, {});
    std::vector<bool> left(8, false);
    left[0] = true;
    count_line("range_left", "range", range, range_keys, left);
  }

  // The live blocks.
  for (unsigned live : {0u, 2u, 3u, 5u, 6u, 7u, 8u})
    std::printf("LKP_LIVE_BLOCKS live=%u blocks=%s\n", live,
                blocks_str(lkp_live_blocks(live)).c_str());

  // One block of a product-form vector on the multiplicities.
  {
    Tensor v;
    v.scalar = mk(3);
    for (unsigned t = 0; t < 5; t++) v.push(mk(10 + t), mk(20 + t));
    for (const auto &block : lkp_live_blocks(6)) {
      const Tensor part = lkp_on_block(v, 3, block);
      std::vector<E> at;
      for (u64 j = 0; j < 32; j++) at.push_back(part.at(j));
      std::printf("LKP_ON_BLOCK block=%u:%u scalar=%s vars=%u part_scalar=%s at=%s\n", block.first,
                  block.second, e_str(v.scalar).c_str(), part.vars(), e_str(part.scalar).c_str(),
                  es_str(at).c_str());
    }
  }
  return 0;
}
