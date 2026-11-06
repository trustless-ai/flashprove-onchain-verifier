// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for the verifier's side of FOLDEQ: the placement of a vector in a table, the committed
// table's public data, its name and tree, the record's seeds and bytes, a key's bytes and faults,
// the public bytes of the shape, and the folded row's record and column claims on G_u. Build with
// -DBLK_FIELD=2. The Rust test in fp-host/tests/foldeq_vectors.rs replays every line.

#include "iop/foldeq.h"

#include <cstdio>
#include <string>
#include <vector>

using namespace blk;

namespace {
E e(u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; }
void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
void pve(const char *name, const E &x) {
  std::printf("%s=", name);
  pv(x);
}
void pd(const char *name, const Digest &d) {
  std::printf("%s=", name);
  for (int i = 0; i < 8; i++) std::printf("%08x", d.w[i]);
}
void pe_list(const char *name, const std::vector<E> &v) {
  std::printf("%s=", name);
  if (v.empty()) std::printf("-");
  for (size_t i = 0; i < v.size(); i++) {
    if (i) std::printf(";");
    pv(v[i]);
  }
}
void pf_list(const char *name, const std::vector<F> &v) {
  std::printf("%s=", name);
  if (v.empty()) std::printf("-");
  for (size_t i = 0; i < v.size(); i++) {
    if (i) std::printf(",");
    std::printf("%016llx", (unsigned long long)v[i].v);
  }
}
void phex(const char *name, const std::vector<u8> &b) {
  std::printf("%s=", name);
  if (b.empty()) std::printf("-");
  for (u8 x : b) std::printf("%02x", x);
}
std::string sane(const char *s) {
  std::string out(s);
  for (char &c : out)
    if (c == ' ') c = '_';
  return out;
}
void pfault(const char *name, const char *f) {
  std::printf("%s=", name);
  if (f == nullptr) {
    std::printf("-");
  } else {
    for (const char *p = f; *p; p++) std::printf("%c", *p == ' ' ? '_' : *p);
  }
}
Digest make_digest(u32 seed) {
  Digest d{};
  for (int i = 0; i < 8; i++) d.w[i] = seed * 0x9E3779B9u + (u32)i * 0x85EBCA6Bu;
  return d;
}
OracleShape plain_shape(CodeId code, size_t rows, unsigned deg, size_t mask_rows, CodeId mask_code, unsigned answers) {
  OracleShape s;
  s.code = code;
  s.main_rows = rows;
  s.main_deg = deg;
  s.mask_rows = mask_rows;
  s.mask_code = mask_code;
  s.answers = answers;
  return s;
}
void lay_line(const char *n, const Codes &codes, const OracleShape &s, bool rows_high, const std::vector<E> &z) {
  const VectorLay lay = vector_lay(codes, s, rows_high);
  const u64 room = vector_room(codes, s, rows_high);
  std::printf("%s_ROW_BITS=%u %s_PLACE_BITS=%u %s_BITS=%u %s_ROOM=%llu\n", n, lay.row_bits, n,
              lay.place_bits, n, lay.bits(), n, (unsigned long long)room);
  std::printf("%s_INDEX=", n);
  for (u64 j = 0; j < (u64(1) << lay.bits()); j++) {
    if (j) std::printf(",");
    std::printf("%llu", (unsigned long long)lay.index(j));
  }
  std::printf("\n%s_ENTRY_AT=", n);
  for (u64 j = 0; j < (u64(1) << lay.bits()); j++) {
    if (j) std::printf(",");
    std::printf("%llu", (unsigned long long)lay.entry_at(j));
  }
  std::printf("\n");
  std::vector<E> at;
  for (u64 j = 0; j < (u64(1) << lay.bits()); j++) at.push_back(lay.on_table(Tensor::eq(z.data(), 3)).at(j));
  pe_list((std::string(n) + "_ON_TABLE").c_str(), at);
  std::printf("\n");
}
void prow(const char *n, OracleId o, const Row &row, unsigned bits) {
  std::printf("%s_KIND=%u %s_NAME=%s ", n, (unsigned)row.kind, n, sane(row.name.c_str()).c_str());
  pve((std::string(n) + "_TARGET").c_str(), row.target);
  std::printf(" %s_COEF=", n);
  for (u64 j = 0; j < (u64(1) << bits); j++) {
    if (j) std::printf(";");
    pv(row.coefficient(o, Part::MAIN, j));
  }
  std::printf("\n");
}
} // namespace

int main() {
  Codes codes;
  codes.base.push_back(Code{4, 8, 4});
  codes.mask.push_back(Code{3, 4, 2});

  // Placement: power-of-two and not, real and virtual rows, rows_high both ways.
  const std::vector<E> z = {e(11), e(12), e(13)};
  lay_line("LAY_A", codes, plain_shape(0, 4, 3, 0, 0, 1), false, z);
  lay_line("LAY_B", codes, plain_shape(0, 3, 3, 0, 0, 1), false, z);
  lay_line("LAY_C", codes, plain_shape(0, 3, 3, 0, 0, 1), true, z);
  lay_line("LAY_D", codes, plain_shape(0, 4, 3, 0, 0, 2), true, z);

  // The committed table's public numbers and faults.
  IndexShape A;
  A.code = Code{4, 8, 4};
  A.v = 2;
  A.answers = 2;
  A.salt_bytes = 40;
  A.distances = TableDistances{3, 4, 5, 6};
  std::printf("IDX_ROWS=%llu IDX_PADS=%zu IDX_PLAIN=%zu IDX_CUBE_BITS=%u\n",
              (unsigned long long)A.rows(), A.pads(), A.plain(), A.cube_bits());
  std::printf("IDX_PAD_PLACE=");
  for (unsigned a = 0; a < A.answers; a++)
    for (unsigned t = 0; t < E_DEGREE; t++) {
      if (a || t) std::printf(",");
      std::printf("%llu", (unsigned long long)A.pad_place(a, t));
    }
  std::printf("\n");
  pfault("IDX_FAULT_A", index_fault(A));
  std::printf("\n");
  {
    IndexShape s = A;
    s.code = Code{0, 0, 0};
    pfault("IDX_FAULT_CODE", index_fault(s));
    std::printf("\n");
    s = A;
    s.v = 41;
    pfault("IDX_FAULT_ROWS", index_fault(s));
    std::printf("\n");
    s = A;
    s.code = Code{4, 4, 2};
    pfault("IDX_FAULT_PADS", index_fault(s));
    std::printf("\n");
    s = A;
    s.salt_bytes = 39;
    pfault("IDX_FAULT_SALT", index_fault(s));
    std::printf("\n");
    s = A;
    s.answers = 0;
    pfault("IDX_FAULT_ANSWERS", index_fault(s));
    std::printf("\n");
  }
  {
    const PricedTable t = priced_table(A, TableTest::ONE_TIME);
    std::printf("PRICED_A_LOG_N=%u PRICED_A_ELL=%llu PRICED_A_R=%llu PRICED_A_V=%u PRICED_A_ANSWERS=%u "
                "PRICED_A_DIST=%llu,%llu,%llu,%llu PRICED_A_TEST=%u PRICED_A_SAID=%d\n",
                t.code.log_n, (unsigned long long)t.code.ell, (unsigned long long)t.code.r, t.v, t.answers,
                (unsigned long long)t.distances.radius, (unsigned long long)t.distances.later_radius,
                (unsigned long long)t.distances.m_once, (unsigned long long)t.distances.m_later, (unsigned)t.test,
                (int)t.said);
  }

  // The table's name, bytes and tree.
  const Digest root = make_digest(0xA1);
  const Digest config = make_digest(0xC0);
  phex("NAME_A", index_name(root, A, config));
  std::printf("\n");
  phex("DIGEST_ROOT", digest_bytes(root));
  std::printf("\n");
  {
    const OracleTreeShape t = index_tree(A, config);
    std::printf("TREE_A_LOG_N=%u TREE_A_LOG_N_ZK=%u TREE_A_MAIN=%zu TREE_A_MASK=%zu TREE_A_NUMBER=%u "
                "TREE_A_SALT=%zu TREE_A_STORED=%d ",
                t.log_n, t.log_n_zk, t.main_symbols[0], t.mask_symbols[0], t.tree_number, t.salt_bytes,
                (int)t.stored);
    pd("TREE_A_RUN", t.run);
    std::printf(" ");
    pd("TREE_A_PARAMS", t.parameters);
    std::printf("\n");
  }

  // The record: seeds, bytes, faults.
  const std::vector<u8> name = {'f', 'o', 'l', 'd', 'e', 'q', '-', 'v', 'e', 'c'};
  phex("SEED_NAME", name);
  std::printf("\n");
  IndexRecord recA;
  for (size_t i = 0; i < 8; i++) recA.y.push_back(e(1000 + i));
  const std::vector<SampleSeed> seeds = record_seeds(A, name);
  std::printf("SEED_COUNT=%zu\n", seeds.size());
  for (size_t i = 0; i < seeds.size(); i++) {
    const std::string p = "SEED_" + std::to_string(i);
    pe_list((p + "_Z").c_str(), seeds[i].z);
    std::printf(" ");
    pve((p + "_BETA").c_str(), seeds[i].beta);
    std::printf("\n");
  }
  phex("RECORD_BYTES", record_bytes(recA));
  std::printf("\n");
  pfault("RECORD_FAULT_A", record_fault(A, recA));
  std::printf("\n");
  {
    IndexRecord short_rec;
    short_rec.y.resize(7);
    pfault("RECORD_FAULT_SHORT", record_fault(A, short_rec));
    std::printf("\n");
  }

  // Public bytes of the bound values.
  phex("PUB_SEED_BYTES", [&] {
    Writer w;
    public_bytes(w, seeds[0]);
    return w.bytes();
  }());
  std::printf("\n");
  pfault("PUB_SEED_FAULT", public_fault(seeds[0]));
  std::printf("\n");
  {
    SampleSeed bad;
    bad.z = seeds[0].z;
    bad.beta = E::zero();
    pfault("PUB_SEED_FAULT_ZERO", public_fault(bad));
    std::printf("\n");
  }
  phex("PUB_INDEX_BYTES", [&] {
    Writer w;
    public_bytes(w, A);
    return w.bytes();
  }());
  std::printf("\n");
  pfault("PUB_INDEX_FAULT", public_fault(A));
  std::printf("\n");
  phex("PUB_RECORD_BYTES", [&] {
    Writer w;
    public_bytes(w, recA);
    return w.bytes();
  }());
  std::printf("\n");
  pfault("PUB_RECORD_FAULT", public_fault(recA));
  std::printf("\n");
  {
    IndexName n;
    n.commitment = digest_bytes(root);
    n.record = recA;
    phex("PUB_NAME_BYTES", [&] {
      Writer w;
      public_bytes(w, n);
      return w.bytes();
    }());
    std::printf("\n");
    pfault("PUB_NAME_FAULT", public_fault(n));
    std::printf("\n");
    IndexName empty;
    empty.record = recA;
    pfault("PUB_NAME_FAULT_EMPTY", public_fault(empty));
    std::printf("\n");
    IndexName short_name;
    short_name.commitment = digest_bytes(root);
    short_name.record.y.resize(7);
    pfault("PUB_NAME_FAULT_RECORD", public_fault(short_name));
    std::printf("\n");
  }

  // A key: bytes and faults.
  {
    IndexKey key(A, config, root, recA);
    phex("KEY_COMMITMENT", key.commitment());
    std::printf("\n");
    phex("KEY_NAME", key.name());
    std::printf("\n");
    pd("KEY_CONFIG", key.configuration());
    std::printf("\n");
    pfault("KEY_FAULT", key.fault());
    std::printf("\n");
    pfault("KEY_FAULT_FN", index_key_fault(key));
    std::printf("\n");
    phex("KEY_RECORD_BYTES", record_bytes(key.record()));
    std::printf("\n");

    IndexKey no_config(A, Digest{}, root, recA);
    pfault("KEY_FAULT_NO_CONFIG", index_key_fault(no_config));
    std::printf("\n");
    IndexRecord short_rec;
    short_rec.y.resize(7);
    IndexKey bad_rec(A, config, root, short_rec);
    pfault("KEY_FAULT_BAD_RECORD", index_key_fault(bad_rec));
    std::printf("\n");
    IndexKey none;
    pfault("KEY_FAULT_DEFAULT", index_key_fault(none));
    std::printf("\n");
  }

  // FOLDEQ's shape: G_u folds the table's rows at gamma.
  FoldeqShape S;
  S.index = A;
  S.u = plain_shape(0, 4, 3, 0, 0, 1);
  S.u.name = "folded row";
  S.rows_high = false;
  S.leaf_class = 7;
  S.columns = 5;
  std::printf("FOLD_TAIL_FIRST=%llu FOLD_ENTRIES=%llu\n", (unsigned long long)S.tail_first(),
              (unsigned long long)S.entries());
  phex("FOLD_PUBLIC_BYTES", [&] {
    Writer w;
    public_bytes(w, S);
    return w.bytes();
  }());
  std::printf("\n");
  pfault("FOLD_PUBLIC_FAULT", public_fault(S));
  std::printf("\n");
  pfault("FOLD_FAULT", foldeq_fault(codes, S));
  std::printf("\n");
  {
    FoldeqShape s = S;
    s.u.main_rows = 0;
    pfault("FOLD_FAULT_NO_ROWS", foldeq_fault(codes, s));
    std::printf("\n");
    s = S;
    s.u.main_deg = 1;
    pfault("FOLD_FAULT_DEG", foldeq_fault(codes, s));
    std::printf("\n");
    s = S;
    s.u.answers = 0;
    pfault("FOLD_FAULT_NO_SAMPLE", foldeq_fault(codes, s));
    std::printf("\n");
    s = S;
    s.columns = 0;
    pfault("FOLD_FAULT_NO_COLUMNS", foldeq_fault(codes, s));
    std::printf("\n");
    s = S;
    s.u.code = 5;
    pfault("FOLD_FAULT_CODE", foldeq_fault(codes, s));
    std::printf("\n");
    s = S;
    s.u.main_rows = 1;
    pfault("FOLD_FAULT_ROOM", foldeq_fault(codes, s));
    std::printf("\n");
    s = S;
    s.index.salt_bytes = 39;
    pfault("FOLD_FAULT_INDEX", foldeq_fault(codes, s));
    std::printf("\n");
  }

  // record_value and block_sums.
  {
    std::vector<F> mf;
    std::vector<E> me;
    for (size_t i = 0; i < A.code.ell; i++) {
      mf.push_back(F{500 + i});
      me.push_back(e(700 + i));
    }
    for (unsigned answer = 0; answer < A.answers; answer++) {
      pve(("RECORD_VALUE_F_" + std::to_string(answer)).c_str(), record_value(A, seeds[0], answer, mf.data()));
      std::printf(" ");
      pve(("RECORD_VALUE_E_" + std::to_string(answer)).c_str(), record_value(A, seeds[0], answer, me.data()));
      std::printf("\n");
    }
    std::vector<E> low = {e(31), e(32)};
    std::vector<E> message;
    for (size_t i = 0; i < 8; i++) message.push_back(e(900 + i));
    BlockSums b;
    b.low = low.data();
    b.k_lo = 2;
    b.count = 2;
    block_sums(message, b);
    pe_list("BLOCK_LOW", low);
    std::printf(" BLOCK_SUMS=");
    for (size_t i = 0; i < b.sums.size(); i++) {
      if (i) std::printf(";");
      pv(b.sums[i]);
    }
    std::printf("\n");
  }

  // The folded row's claims on G_u, for both placements.
  const std::vector<E> gamma = {e(21), e(22)};
  const std::vector<E> eq_gamma = foldeq_weights(S, gamma.data());
  pe_list("FOLD_EQ_GAMMA", eq_gamma);
  std::printf("\n");
  const std::vector<F> column = {F{101}, F{102}, F{103}, F{104}};
  pve("FOLD_SYMBOL", foldeq_symbol(eq_gamma, column.data()));
  std::printf("\n");
  pe_list("FOLD_RECORD_Y", recA.y);
  std::printf("\n");
  {
    Statement st(codes);
    const OracleId oracle = st.sent(S.u);
    std::printf("FOLD_ORACLE=%u\n", oracle);
    for (int rh = 0; rh < 2; rh++) {
      FoldeqShape s = S;
      s.rows_high = rh != 0;
      const VectorLay lay = vector_lay(codes, s.u, s.rows_high);
      FoldedRow at{oracle, lay};
      std::printf("FOLD_RH%d_ROW_BITS=%u FOLD_RH%d_PLACE_BITS=%u FOLD_RH%d_BITS=%u\n", rh, lay.row_bits, rh,
                  lay.place_bits, rh, lay.bits());
      for (unsigned i = 0; i < s.index.answers; i++) {
        const Row row = foldeq_record_row(s, seeds[i], recA, i, eq_gamma, at);
        prow(("FOLD_RH" + std::to_string(rh) + "_REC" + std::to_string(i)).c_str(), oracle, row, lay.bits());
      }
      for (u64 x : {u64(0), u64(7), u64(15)}) {
        const E y = e(550 + x);
        const Row row = foldeq_column_row(s, x, y, at);
        const std::string p = "FOLD_RH" + std::to_string(rh) + "_COL" + std::to_string(x);
        std::printf("%s_Y=", p.c_str());
        pv(y);
        std::printf(" ");
        prow(p.c_str(), oracle, row, lay.bits());
      }
    }
  }
  return 0;
}
