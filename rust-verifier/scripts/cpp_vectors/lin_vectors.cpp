// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for LIN (blocks/iop/lin.h), verifier side: LinShape and its faults, the three prover
// messages' oracle notices, the claims (Eval), (Fold) and (Dot), VectorLay, and the binding tree
// (LinBindingShape, the leaf/vertex hashes and lin_binding_root). Build with -DBLK_FIELD=2.

#include "iop/lin.h"

#include <cstdio>
#include <vector>

using namespace blk;

namespace {
E e(u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; }
void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
void phex(const std::vector<u8> &b) {
  if (b.empty()) std::printf("-");
  for (u8 x : b) std::printf("%02x", x);
}
Digest make_digest(u32 seed) {
  Digest d{};
  for (int i = 0; i < 8; i++) d.w[i] = seed * 0x9E3779B9u + (u32)i * 0x85EBCA6Bu;
  return d;
}
void pd(const char *name, const Digest &d) {
  std::printf("%s=", name);
  for (int i = 0; i < 8; i++) std::printf("%08x", d.w[i]);
}
u8 salt_byte(u64 pos, size_t k) { return (u8)((pos * 31 + k * 7 + 5) & 0xFF); }

Codes toy_codes() {
  Codes codes;
  codes.base.push_back(Code{4, 8, 1});
  codes.base.push_back(Code{4, 4, 1});
  codes.base.push_back(Code{4, 2, 1});
  codes.mask.push_back(Code{4, 4, 1});
  return codes;
}

std::vector<IoppStage> stages(CodeId code) {
  return {IoppStage{code, 0, 2, 1}, IoppStage{code, 0, 0, 0}};
}

OracleShape main_shape(const char *name, CodeId code, size_t rows) {
  OracleShape s;
  s.name = name;
  s.code = code;
  s.main_rows = rows;
  s.main_deg = E_DEGREE;
  s.answers = 1;
  return s;
}
OracleShape split_shape(const char *name, size_t mask_rows) {
  OracleShape s;
  s.name = name;
  s.main_rows = 0;
  s.mask_rows = mask_rows;
  s.mask_code = 0;
  s.answers = 1;
  return s;
}

// The base shape: one code for G_u, Omega and W, so neither split is needed.
LinShape make_s0() {
  LinShape S;
  S.fold.index.code = Code{4, 8, 1};
  S.fold.index.v = 2;
  S.fold.index.answers = 1;
  S.fold.index.salt_bytes = 40;
  S.fold.u = main_shape("G_u", 0, 2);
  S.fold.columns = 4;
  S.k_lo = 0;
  S.matrix_rows = 5;
  S.omega = main_shape("Omega", 0, 2);
  S.w = main_shape("W", 0, 2);
  S.shared_mask_code = 0;
  S.own_mask_code = 0;
  S.masks_ahead = false;
  S.test_u = stages(0);
  S.test_omega = stages(0);
  S.test_own = stages(0);
  S.test_own_omega = stages(0);
  return S;
}

// The shape with both splits needed: G_u and W use code 0, Omega code 1.
LinShape make_s1() {
  LinShape S = make_s0();
  S.omega = main_shape("Omega", 1, 2);
  S.shared_split = split_shape("shared split", 2);
  S.own_split = split_shape("own split", 2);
  S.masks_ahead = true;
  S.test_omega = stages(1);
  S.test_own_omega = stages(1);
  S.choice.masks_ride = true;
  return S;
}

void print_shape(const char *name, const LinShape &S) {
  std::printf(
      "SHAPE %s k_col=%u k_row=%u shared_split=%d own_split=%d entries=%llu masks_ahead=%d "
      "test_u=%zu test_omega=%zu test_own=%zu test_own_omega=%zu\n",
      name, S.k_col(), S.k_row(), (int)S.shared_split_needed(), (int)S.own_split_needed(),
      (unsigned long long)S.fold.entries(), (int)S.masks_ahead, S.test_u.size(), S.test_omega.size(),
      S.test_own.size(), S.test_own_omega.size());
}

void print_bytes(const char *tag, const LinShape &S) {
  Writer w;
  public_bytes(w, S);
  std::printf("%s bytes=", tag);
  phex(w.bytes());
  std::printf("\n");
}

void print_message(const char *tag, const std::vector<OracleNotice> &m) {
  std::printf("%s count=%zu", tag, m.size());
  for (const OracleNotice &n : m) {
    Writer w;
    public_bytes(w, n);
    std::printf(" ");
    phex(w.bytes());
  }
  std::printf("\n");
}

void print_room(const char *name, const Codes &codes, const OracleShape &s, bool high, bool dir) {
  std::printf("ROOM %s rows_high=%d room=%llu\n", name, (int)high,
              (unsigned long long)vector_room(codes, s, high));
  (void)dir;
}

void print_lay(const Codes &codes, const char *name, const OracleShape &s, bool high, const std::vector<E> &p) {
  const VectorLay lay = vector_lay(codes, s, high);
  std::printf("LAY %s rows_high=%d row_bits=%u place_bits=%u bits=%u\n", name, (int)high, lay.row_bits,
              lay.place_bits, lay.bits());
  std::printf("INDEX");
  for (u64 j = 0; j < (u64(1) << lay.bits()); j++) std::printf(" %llu:%llu", (unsigned long long)j, (unsigned long long)lay.index(j));
  std::printf("\nENTRY");
  for (u64 i = 0; i < (u64(1) << lay.bits()); i++) std::printf(" %llu:%llu", (unsigned long long)i, (unsigned long long)lay.entry_at(i));
  std::printf("\nON_TABLE");
  const Tensor v = Tensor::eq(p.data(), 2, e(7));
  const Tensor on = lay.on_table(v);
  for (u64 j = 0; j < (u64(1) << lay.bits()); j++) {
    std::printf(" ");
    pv(on.at(j));
  }
  std::printf("\n");
}

void print_row(const char *tag, const Row &row, const std::vector<std::pair<OracleId, const VectorLay *>> &who) {
  std::printf("ROW %s name=%s target=", tag, row.name.c_str());
  pv(row.target);
  std::printf("\nUNIT");
  for (const Unit &u : row.units) {
    std::printf(" %u:%u:%llu:", u.oracle, (unsigned)u.part, (unsigned long long)u.index);
    pv(u.coeff);
  }
  std::printf("\n");
  for (const auto &[o, lay] : who) {
    std::printf("COEF o=%u", o);
    for (u64 j = 0; j < (u64(1) << lay->bits()); j++) {
      std::printf(" ");
      pv(row.coefficient(o, Part::MAIN, j));
    }
    std::printf("\n");
  }
}

void print_fault(const char *name, const Codes &codes, const LinShape &S) {
  const char *f = lin_fault(codes, S);
  std::printf("FAULT %s fault=%s\n", name, f ? f : "NULL");
}
} // namespace

int main() {
  const Codes codes = toy_codes();
  const LinShape S0 = make_s0();
  LinShape S1 = make_s1();

  print_shape("S0", S0);
  print_shape("S1", S1);
  print_bytes("SHAPEBYTES S0", S0);
  print_bytes("SHAPEBYTES S1", S1);

  print_message("MESSAGE S0 w", lin_message_w(S0));
  print_message("MESSAGE S0 u", lin_message_u(S0));
  print_message("MESSAGE S0 omega", lin_message_omega(S0));
  print_message("MESSAGE S1 w", lin_message_w(S1));
  print_message("MESSAGE S1 u", lin_message_u(S1));
  print_message("MESSAGE S1 omega", lin_message_omega(S1));

  const FoldShape F = lin_fold_shape(S1.test_own, S1.w_leaf_class);
  std::printf("FOLD_SHAPE code=%u mask_code=%u k=%u h=%u mask_leaf_class=%u\n", F.code, F.mask_code,
              F.layout.k, F.layout.h, F.mask_leaf_class);

  const std::vector<E> point = {e(501), e(502)};
  const std::vector<E> omega_p = {e(601), e(602)};
  print_room("omega_S0", codes, S0.omega, S0.omega_rows_high, false);
  print_room("w_S0", codes, S0.w, S0.w_rows_high, false);
  print_room("u_S0", codes, S0.fold.u, S0.fold.rows_high, false);
  print_room("omega_S1", codes, S1.omega, S1.omega_rows_high, false);
  print_lay(codes, "omega_S0", S0.omega, false, point);
  print_lay(codes, "omega_S0", S0.omega, true, point);
  print_lay(codes, "omega_S1", S1.omega, false, point);
  print_lay(codes, "w_S0", S0.w, false, point);
  print_lay(codes, "u_S0", S0.fold.u, false, point);
  (void)omega_p;

  const VectorLay omega_lay = vector_lay(codes, S0.omega, S0.omega_rows_high);
  const VectorLay w_lay = vector_lay(codes, S0.w, S0.w_rows_high);
  const FoldedRow u{3, vector_lay(codes, S0.fold.u, S0.fold.rows_high)};

  const std::vector<E> gp1 = {e(301), e(302), e(303)};
  const std::vector<E> gp2 = {e(401), e(402), e(403)};
  LinClaim claim;
  claim.g.push_back(Tensor::eq(gp1.data(), 3, e(11)));
  claim.g.push_back(Tensor::eq(gp2.data(), 3, e(12)));
  claim.psi = {e(101), e(102)};
  claim.masks.push_back(Unit{4, Part::MASK, 7, e(13)});
  claim.masks.push_back(Unit{4, Part::MASK, 9, e(14)});
  claim.target = e(15);

  const std::vector<E> zeta = {e(201), e(202), e(203)};
  const std::vector<std::pair<OracleId, const VectorLay *>> eval_who = {{1, &w_lay}};
  const std::vector<std::pair<OracleId, const VectorLay *>> fold_who = {{2, &omega_lay}, {3, &u.lay}};
  const std::vector<std::pair<OracleId, const VectorLay *>> dot_who = {{2, &omega_lay}, {1, &w_lay}};
  print_row("eval", lin_eval_row(S0, claim, 1, w_lay), eval_who);
  print_row("fold", lin_fold_row(S0, claim.psi, zeta, u, 2, omega_lay), fold_who);
  print_row("dot", lin_dot_row(S0, claim.g, claim.psi, 2, omega_lay, 1, w_lay), dot_who);

  print_fault("S0", codes, S0);
  print_fault("S1", codes, S1);
  {
    LinShape S = S0;
    S.matrix_rows = 0;
    print_fault("matrix_zero", codes, S);
  }
  {
    LinShape S = S0;
    S.k_lo = 31;
    print_fault("k_lo_high", codes, S);
  }
  {
    LinShape S = S0;
    S.fold.columns = 0;
    print_fault("fold_columns", codes, S);
  }
  {
    LinShape S = S0;
    S.omega.main_deg = 1;
    print_fault("omega_deg", codes, S);
  }
  {
    LinShape S = S0;
    S.omega.answers = 0;
    print_fault("omega_answers", codes, S);
  }
  {
    LinShape S = S0;
    S.omega.mask_rows = 1;
    print_fault("omega_mask", codes, S);
  }
  {
    LinShape S = S0;
    S.matrix_rows = 6;
    print_fault("matrix_fit", codes, S);
  }
  {
    LinShape S = S1;
    S.shared_split_leaf_class = S.omega_leaf_class;
    print_fault("shared_leaf", codes, S);
  }
  {
    LinShape S = S1;
    S.own_split_leaf_class = S.w_leaf_class;
    print_fault("own_leaf", codes, S);
  }
  {
    LinShape S = S1;
    S.shared_split.main_rows = 1;
    print_fault("split_main", codes, S);
  }
  {
    LinShape S = S1;
    S.omega.code = 9;
    print_fault("omega_code", codes, S);
  }
  {
    LinShape S = S1;
    S.w.code = 9;
    print_fault("w_code", codes, S);
  }
  {
    LinShape S = S0;
    S.shared_mask_code = 9;
    print_fault("mask_code", codes, S);
  }
  {
    LinShape S = S1;
    S.w = main_shape("W", 2, 1);
    print_fault("w_room", codes, S);
  }
  {
    LinShape S = S0;
    S.fold.u.main_rows = 1;
    print_fault("u_room", codes, S);
  }

  // The binding tree: a salted leaf, its path and the root it leads to.
  LinBindingShape bs;
  bs.log_leaves = 3;
  bs.salt_bytes = 40;
  {
    Writer w;
    public_bytes(w, bs);
    std::printf("BINDING_SHAPE log_leaves=%u salt_bytes=%zu fault=%s bytes=", bs.log_leaves,
                bs.salt_bytes, public_fault(bs) ? public_fault(bs) : "NULL");
    phex(w.bytes());
    std::printf("\n");
  }
  {
    LinBindingShape deep = bs;
    deep.log_leaves = 49;
    LinBindingShape salt = bs;
    salt.salt_bytes = 39;
    std::printf("BINDING_FAULT deep=%s\n", public_fault(deep));
    std::printf("BINDING_FAULT salt=%s\n", public_fault(salt));
  }

  const Digest configuration = make_digest(1);
  const Digest seal = make_digest(2);
  const Digest left = make_digest(51);
  const Digest right = make_digest(52);
  std::printf("VERTEX ");
  pd("left", left);
  std::printf(" ");
  pd("right", right);
  std::printf(" ");
  pd("digest", lin_binding_vertex(configuration, left, right));
  std::printf("\n");

  std::vector<u8> salt(bs.salt_bytes);
  for (size_t k = 0; k < salt.size(); k++) salt[k] = salt_byte(5, k);
  std::printf("LEAF place=5 salt=");
  phex(salt);
  std::printf(" ");
  pd("digest", lin_binding_leaf(bs, configuration, 5, seal, salt.data()));
  std::printf("\n");

  const Digest sib3 = make_digest(41);
  const Digest sib2 = make_digest(42);
  const Digest sib1 = make_digest(43);
  Writer pw;
  pw.put_u64(5);
  pw.put_bytes(salt.data(), salt.size());
  pw.put(sib3);
  pw.put(sib2);
  pw.put(sib1);
  std::printf("PATH bytes=");
  phex(pw.bytes());
  std::printf(" ");
  pd("sib3", sib3);
  std::printf(" ");
  pd("sib2", sib2);
  std::printf(" ");
  pd("sib1", sib1);
  std::printf("\n");
  {
    Reader r(pw.data(), pw.size());
    LinBindingRoot out;
    const bool ok = lin_binding_root(r, bs, configuration, seal, out);
    std::printf("ROOT ok=%d at_end=%d places=%llu ", (int)ok, (int)r.at_end(),
                (unsigned long long)out.places());
    pd("digest", out.digest());
    std::printf("\n");
  }
  {
    Writer bw;
    bw.put_u64(8);
    bw.put_bytes(salt.data(), salt.size());
    bw.put(sib3);
    Reader r(bw.data(), bw.size());
    LinBindingRoot out;
    const bool ok = lin_binding_root(r, bs, configuration, seal, out);
    std::printf("ROOT_BAD place=8 ok=%d\n", (int)ok);
  }
  {
    Writer tw;
    tw.put_u64(5);
    tw.put_bytes(salt.data(), salt.size());
    Reader r(tw.data(), tw.size());
    LinBindingRoot out;
    const bool ok = lin_binding_root(r, bs, configuration, seal, out);
    std::printf("ROOT_BAD short ok=%d\n", (int)ok);
  }
  {
    LinBindingShape one;
    one.log_leaves = 0;
    one.salt_bytes = 40;
    std::vector<u8> s0(one.salt_bytes);
    for (size_t k = 0; k < s0.size(); k++) s0[k] = salt_byte(0, k);
    Writer w0;
    w0.put_u64(0);
    w0.put_bytes(s0.data(), s0.size());
    std::printf("PATH0 bytes=");
    phex(w0.bytes());
    std::printf("\n");
    Reader r(w0.data(), w0.size());
    LinBindingRoot out;
    const bool ok = lin_binding_root(r, one, configuration, seal, out);
    std::printf("ROOT0 ok=%d places=%llu ", (int)ok, (unsigned long long)out.places());
    pd("digest", out.digest());
    std::printf("\n");
  }
  {
    const Digest made = make_digest(77);
    const LinBindingRoot out = LinBindingRoot::made_up_without_a_tree(made, 6);
    std::printf("MADE_UP places=%llu ", (unsigned long long)out.places());
    pd("digest", out.digest());
    std::printf("\n");
  }
  return 0;
}
