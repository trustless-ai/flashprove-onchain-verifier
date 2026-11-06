// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for RNG (`blocks/iop/rng.h`): the shape's faults, the lookup's public inputs, the
// multiplicities' layout, the claim on the keys, Theta from a real channel, the batched row, and
// the plan's combinations check. Build with -DBLK_FIELD=2.

#define BLK_PLANS_BY_HAND_FOR_A_TEST

#include "chain/rounds.h"
#include "hash/hash.h"
#include "iop/rng.h"
#include "numbers/plan.h"

#include <cstdio>
#include <string>
#include <utility>
#include <vector>

using namespace blk;

namespace {
E e(u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; }
void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
void peq(const char *name, const E &x) {
  std::printf("%s=", name);
  pv(x);
}
void phex(const std::vector<u8> &b) {
  if (b.empty()) std::printf("-");
  for (u8 x : b) std::printf("%02x", x);
}

} // namespace

int main() {
  // ---- the shapes ----
  // A: N = Np = 2, one matrix of 2 rows and 2 columns, one read of length 1. The lookup's table
  // has 4 rows; its multiplicities are planes = 4, mu = 2, live = 0 (all), no padding.
  RngShape A;
  A.lanes = 2, A.log_radix = 3, A.digit_bits[0] = 1, A.digit_bits[1] = 1, A.combinations = 2;
  {
    RngMatrix m;
    m.rows = 2, m.columns = 2, m.packed = 0;
    // 1 packed row, 2 columns: (i' = 0, c = 0..1) in row 0, places 0..1.
    m.laid = {LaidBlock{0, 0, 0, 0, 0, 1, 0, 1, true}};
    A.matrices = {m};
  }
  A.reads = {RngRead{0, 1}};
  A.reads_in = 1;
  A.reads_laid = {LaidBlock{0, 0, 0, 0, 0, 1, 0, 1, true}};  // one row of 2 entries
  A.digit_columns = 2;
  {
    OracleShape d;
    d.name = "digits";
    d.code = 1;  // ell = 4, so 2 row bits and 2 place bits
    d.main_rows = 4;
    d.main_deg = 1;
    d.mask_rows = 0;
    d.answers = 0;
    A.digits = OracleNotice{d, 0};
    // N = 2 rows (u) x 2 DC = 4 columns, at rows 0..1 and places 0..3.
    A.digits_laid = {LaidBlock{0, 0, 0, 0, 1, 2, 1, 2, true}};
    OracleShape m;
    m.name = "multiplicities";
    m.code = 2;  // ell = 16: four place bits, rng_planes_places = 4 << 2 = 16
    m.main_rows = 1;
    m.main_deg = 1;
    m.mask_rows = 0;
    m.answers = 0;
    A.multiplicities = OracleNotice{m, 0};
  }
  A.digits_in = 3, A.masks_from = 2;

  // B: N = 3, Np = 4, so the lookup has 5 planes, mu = 3, live = 5 and two runs of padding.
  RngShape B = A;
  B.combinations = 3;
  B.multiplicities.shape.code = 3;  // ell = 32: five place bits
  // N = 3 rows x 4 columns: rows 0..1 in one block, row 2 in a second.
  B.digits_laid = {LaidBlock{0, 0, 0, 0, 1, 2, 1, 2, true}, LaidBlock{2, 0, 2, 0, 0, 2, 0, 2, true}};

  // ---- rng_fault ----
  auto fault = [](const char *name, const RngShape &S) {
    const char *f = rng_fault(S);
    std::printf("FAULT %s %s\n", name, f ? f : "ok");
  };
  fault("good_a", A);
  fault("good_b", B);
  {
    RngShape X = A;
    X.lanes = 0;
    fault("lanes0", X);
  }
  {
    RngShape X = A;
    X.lanes = 65;
    fault("lanes65", X);
  }
  {
    RngShape X = A;
    X.log_radix = 64;
    fault("log_radix64", X);
  }
  {
    RngShape X = A;
    X.digit_bits[0] = 0;
    fault("bit0_zero", X);
  }
  {
    RngShape X = A;
    X.digit_bits[1] = 0;
    fault("bit1_zero", X);
  }
  {
    RngShape X = A;
    X.digit_bits[0] = 2;
    fault("window_too_big", X);
  }
  {
    RngShape X = A;
    X.log_radix = 60;
    fault("wrap", X);
  }
  {
    RngShape X = A;
    X.combinations = 0;
    fault("combinations0", X);
  }
  {
    RngShape X = A;
    X.matrices.clear();
    fault("no_matrix", X);
  }
  {
    RngShape X = A;
    X.matrices[0].rows = 0;
    fault("rows0", X);
  }
  {
    RngShape X = A;
    X.matrices[0].columns = 0;
    fault("columns0", X);
  }
  {
    RngShape X = A;
    X.matrices[0].rows = (u64(1) << 24) + 1;
    fault("rows_most", X);
  }
  {
    RngShape X = A;
    X.matrices[0].columns = (u64(1) << 24) + 1;
    fault("columns_most", X);
  }
  {
    RngShape X = A;
    X.combinations = (u64(1) << 24) + 1;
    fault("combinations_most", X);
  }
  {
    RngShape X = A;
    X.digit_columns = 3;
    fault("digit_columns_not_pow2", X);
  }
  {
    RngShape X = A;
    X.digit_columns = 1;
    fault("digit_columns_small", X);
  }
  {
    RngShape X = A;
    X.matrices[0].packed = X.reads_in;
    fault("packed_is_reads", X);
  }
  {
    RngShape X = A;
    X.reads[0].matrix = 1;
    fault("read_matrix", X);
  }
  {
    RngShape X = A;
    X.reads[0].length = 3;
    fault("read_length", X);
  }
  {
    RngShape X = A;
    X.reads[0].length = 0;
    fault("read_length0", X);
  }
  {
    RngShape X = A;
    X.digits_in = NONE_ID;
    fault("digits_none", X);
  }
  {
    RngShape X = A;
    X.masks_from = NONE_ID;
    fault("masks_none", X);
  }
  {
    RngShape X = A;
    X.masks_from = X.digits_in;
    fault("masks_after", X);
  }
  {
    RngShape X = A;
    X.matrices[0].packed = X.digits_in;
    fault("packed_after", X);
  }
  {
    RngShape X = A;
    X.reads_in = X.digits_in;
    fault("reads_after", X);
  }
  {
    RngShape X = A;
    X.reads.clear();
    X.reads_laid.clear();
    X.reads_in = NONE_ID;
    fault("good_no_reads", X);
  }
  {
    RngShape X = A;
    X.reads.clear();
    X.reads_laid.clear();
    X.reads_in = X.digits_in;  // not checked when there is no read
    fault("good_no_reads_after", X);
  }
  std::printf("PUBLIC_FAULT good_a %s\n", public_fault(A) ? public_fault(A) : "ok");

  // ---- the lookup's public inputs ----
  auto lookup = [](const char *name, const RngShape &S) {
    const LkpPublic L = rng_lookup(S);
    std::printf("LOOKUP %s parts=", name);
    for (size_t i = 0; i < L.parts.size(); i++) std::printf("%s%u", i ? "," : "", L.parts[i]);
    std::printf(" d=%u mu=%u live=%u g=%u shifted=%d planes=%u all_keys=%llu read_from=", L.d, L.mu, L.live,
                L.g, (int)L.shifted, L.planes(), (unsigned long long)L.all_keys());
    for (size_t i = 0; i < L.read_from.size(); i++)
      std::printf("%s%u", i ? "," : "", (unsigned)L.read_from[i]);
    std::printf("\n");
    for (const LkpKeyBlock &b : L.keys)
      std::printf("KEY %s first=%llu log_trees=%u function=%d padding_row=%llu\n", name,
                  (unsigned long long)b.first, b.log_trees, b.function, (unsigned long long)b.padding_row);
    for (const LkpTablePart &t : L.tables)
      std::printf("TABLE %s first=%llu log_rows=%u function=%u rows=%zu\n", name, (unsigned long long)t.first,
                  t.log_rows, t.function, t.rows.size());
    for (const LkpPadding &p : L.padding)
      std::printf("PADDING %s part=%u first=%llu log_step=%u length=%llu row=%llu\n", name, p.part,
                  (unsigned long long)p.first, p.log_step, (unsigned long long)p.length,
                  (unsigned long long)p.row);
    std::printf("PLACES %s %llu\n", name, (unsigned long long)rng_planes_places(L));
    std::printf("LOOKUP_FAULT %s %s\n", name, lkp_fault(L) ? lkp_fault(L) : "ok");
  };
  lookup("a", A);
  lookup("b", B);

  // ---- rng_planes_at: the coefficients on the multiplicities (row 0) ----
  auto planes_at = [](const char *name, const Statement &st, const RngShape &S, const LkpPublic &L) {
    const OracleId o = S.digits_in + 1;
    const unsigned row_bits = st.row_bits(o, Part::MAIN);
    const u64 entries = u64(1) << (row_bits + st.table_bits(o, Part::MAIN) - row_bits);
    std::vector<E> point(L.mu + L.d);
    for (size_t i = 0; i < point.size(); i++) point[i] = e(700 + i);
    Tensor v = Tensor::eq(point.data(), (unsigned)point.size(), E::one());
    Row row;
    rng_planes_at(st, S, L)(row, std::move(v));
    std::printf("PLANES_AT %s entries=%llu places=%llu", name, (unsigned long long)entries,
                (unsigned long long)rng_planes_places(L));
    for (u64 j = 0; j < entries; j++) {
      std::printf(" ");
      pv(row.coefficient(o, Part::MAIN, j));
    }
    std::printf("\n");
  };

  // ---- rng_key_row: the claim on the sent digits ----
  auto key_row = [](const char *name, const Statement &st, const RngShape &S, const LkpPublic &L) {
    LkpKeys k;
    const unsigned bits_j = ceil_log2(S.digit_columns), bits_u = ceil_log2(S.step());
    k.point.resize(1 + bits_j + bits_u);
    for (size_t i = 0; i < k.point.size(); i++) k.point[i] = e(800 + i);
    k.weights.add(Tensor::eq(k.point.data(), (unsigned)k.point.size(), E::one()));
    k.target = e(900);
    Row row = rng_key_row(st, S, std::move(k));
    const OracleId o = S.digits_in;
    const u64 entries = u64(1) << st.table_bits(o, Part::MAIN);
    std::printf("KEY_ROW %s row=%s target=", name, row.name.c_str());
    pv(row.target);
    std::printf("\nKEY_ROW_MAIN %s", name);
    for (u64 j = 0; j < entries; j++) {
      std::printf(" ");
      pv(row.coefficient(o, Part::MAIN, j));
    }
    std::printf("\n");
  };

  // ---- one statement per shape, with the five oracle messages in the order of their ids ----
  Codes codes;
  codes.base.push_back(Code{2, 2, 1});   // id 0: ell = 2
  codes.base.push_back(Code{3, 4, 2});   // id 1: ell = 4
  codes.base.push_back(Code{5, 16, 2});  // id 2: ell = 16
  codes.base.push_back(Code{6, 32, 2});  // id 3: ell = 32
  codes.mask.push_back(Code{2, 2, 1});
  Statement st_a(codes);
  st_a.sent(OracleShape{"packed", 0, A.packed_rows(0), 1, 0, 0, 0});
  st_a.sent(OracleShape{"reads", 1, 1, 1, 0, 0, 0});
  st_a.sent(OracleShape{"masks", 0, 1, 1, 0, 0, 0});
  st_a.sent(A.digits.shape);
  st_a.sent(A.multiplicities.shape);
  Statement st_b(codes);
  st_b.sent(OracleShape{"packed", 0, B.packed_rows(0), 1, 0, 0, 0});
  st_b.sent(OracleShape{"reads", 1, 1, 1, 0, 0, 0});
  st_b.sent(OracleShape{"masks", 0, 1, 1, 0, 0, 0});
  st_b.sent(B.digits.shape);
  st_b.sent(B.multiplicities.shape);

  planes_at("a", st_a, A, rng_lookup(A));
  planes_at("b", st_b, B, rng_lookup(B));
  key_row("a", st_a, A, rng_lookup(A));
  key_row("b", st_b, B, rng_lookup(B));

  // ---- rng_row: the coefficients of the batched equations ----
  auto row = [](const char *name, const Statement &st, const RngShape &S) {
    RngWeights phi = {{e(11)}};
    RngTheta theta(S.all_columns() * S.combinations);
    for (size_t i = 0; i < theta.size(); i++) theta[i] = (signed char)(int(i % 3) - 1);
    const E x = e(13);
    Row row = rng_row(st, S, phi, theta, S.digits_in, x, 3);
    std::printf("ROW %s row=%s target=", name, row.name.c_str());
    pv(row.target);
    std::printf("\n");
    std::printf("ROW_NUMBERS %s equations=%llu step=%llu cell_rows=%llu all_columns=%llu read_first=%llu\n", name,
                (unsigned long long)S.equations(), (unsigned long long)S.step(), (unsigned long long)S.cell_rows(),
                (unsigned long long)S.all_columns(), (unsigned long long)S.read_first(S.reads.size()));
    std::printf("ROW_PACKED %s", name);
    for (u64 j = 0; j < (u64(1) << st.table_bits(0, Part::MAIN)); j++) {
      std::printf(" ");
      pv(row.coefficient(0, Part::MAIN, j));
    }
    std::printf("\n");
    std::printf("ROW_READS %s", name);
    for (u64 j = 0; j < (u64(1) << st.table_bits(1, Part::MAIN)); j++) {
      std::printf(" ");
      pv(row.coefficient(1, Part::MAIN, j));
    }
    std::printf("\n");
    std::printf("ROW_DIGITS %s", name);
    for (u64 j = 0; j < (u64(1) << st.table_bits(S.digits_in, Part::MAIN)); j++) {
      std::printf(" ");
      pv(row.coefficient(S.digits_in, Part::MAIN, j));
    }
    std::printf("\n");
  };
  row("a", st_a, A);
  row("b", st_b, B);

  // ---- rng_weights_check: the shape and the weights agree ----
  {
    RngWeights phi = {{e(11)}};
    rng_weights_check(A, phi);
    std::printf("WEIGHTS a ok\n");
  }

  // ---- rng_plan_fault: the shape and the plan's combinations agree ----
  {
    Setting set = setting_goldilocks();
    auto make = [&set](u64 combinations, const char *name) {
      Plan p(set);
      PlanRound &r = p.close(name, RoundKind::BITS, ErrorKind::SMALL, Bound((u64)0), Priced::ON_THE_CALLERS_WORD);
      r.draw_trits = 4, r.combinations = combinations;
      p.close("seal", RoundKind::SEAL, ErrorKind::ZERO, Bound((u64)0), Priced::NOTHING);
      return p.finish();
    };
    const Planned pa = make(2, R_RNG), pb = make(3, R_RNG), pc = make(2, "other");
    auto plan_fault = [](const char *name, const RngShape &S, const Planned &p) {
      const char *f = rng_plan_fault(S, p);
      std::printf("PLAN_FAULT %s %s\n", name, f ? f : "ok");
    };
    plan_fault("matching", A, pa);
    plan_fault("another_combinations", A, pb);
    plan_fault("no_rng_round", A, pc);
  }

  // ---- rng_theta: a real chain with one bits round ----
  {
    Setting set = setting_goldilocks();
    set.set_work(ErrorKind::QUERY, Scope::REQUEST, 2);
    Plan plan(set);
    PlanRound &r = plan.close(R_RNG, RoundKind::BITS, ErrorKind::SMALL, Bound((u64)0), Priced::ON_THE_CALLERS_WORD);
    r.draw_trits = A.all_columns() * A.combinations, r.combinations = A.combinations;
    plan.close_none("last");
    plan.close("seal", RoundKind::SEAL, ErrorKind::ZERO, Bound((u64)0), Priced::NOTHING);
    const Planned q = plan.finish();
    std::printf("PLAN holds=%d rounds=%zu\n", (int)q->holds(), q->rounds_.size());
    std::printf("SET salt=%u nonce=%u position=%u samples=%u saved=%u target=%u\n", q->set.salt_bytes,
                q->set.nonce_bytes, q->set.position_bytes, q->set.samples, (unsigned)q->set.saved_coefficient,
                q->set.target);
    for (size_t i = 0; i < q->rounds_.size(); i++) {
      const PlanRound &x = q->rounds_[i];
      std::printf("ROUND i=%zu name=%s kind=%u work=%u msg=%llu roots=%u answers=%u draw_e=%llu nz=%llu draw_pos=%llu log_n=%u trits=%llu rows=%llu first_list=%llu combos=%llu sharing=%llu\n",
                  i, x.name.c_str(), (unsigned)x.kind, x.work_bits, (unsigned long long)x.message_bytes, x.roots,
                  x.answers, (unsigned long long)x.draw_E, (unsigned long long)x.draw_nonzero,
                  (unsigned long long)x.draw_positions, x.log_n, (unsigned long long)x.draw_trits,
                  (unsigned long long)x.rows, (unsigned long long)x.first_list,
                  (unsigned long long)x.combinations, (unsigned long long)x.sharing);
    }

    const u64 LABEL = 7;
    Digest config{};
    config.w[0] = 0xC0F1;
    auto bind = [&config](Binder &b) {
      b.configuration(config);
      b.parameter("a", (u64)42);
      b.statement("claim", (u64)7);
    };
    std::printf("BIND label=%llu config=", (unsigned long long)LABEL);
    for (int i = 0; i < 8; i++) std::printf("%08x", config.w[i]);
    std::printf("\n");
    Digest salt{};
    salt.w[0] = 0x5A17;
    std::printf("SALT ");
    for (int i = 0; i < 8; i++) std::printf("%s%08x", i ? "" : "", salt.w[i]);
    std::printf("\n");

    Writer proof;
    {
      Binder b(LABEL, q);
      bind(b);
      ProverRounds ch(b, salt, proof);
      const RngTheta theta = rng_theta(ch, A);
      std::printf("THETA n=%zu v=", theta.size());
      for (size_t i = 0; i < theta.size(); i++) std::printf("%s%d", i ? "," : "", (int)theta[i]);
      std::printf("\n");
      ch.close_empty("last");
      Sealed sealed;
      const bool sok = ch.seal("seal", sealed);
      std::printf("SEAL_PROVER ok=%d\n", (int)sok);
      ch.finish();
    }
    std::printf("PROOF ");
    phex(proof.bytes());
    std::printf("\n");

    {
      Binder b(LABEL, q);
      bind(b);
      Reader r(proof.data(), proof.size());
      VerifierSession session;
      VerifierRounds ch(b, r, session);
      const RngTheta theta = rng_theta(ch, A);
      std::printf("VTHETA n=%zu v=", theta.size());
      for (size_t i = 0; i < theta.size(); i++) std::printf("%s%d", i ? "," : "", (int)theta[i]);
      std::printf("\n");
      ch.close_empty("last");
      Sealed sealed;
      const bool sok = ch.seal("seal", sealed);
      const bool fin = ch.finish();
      std::printf("SEAL_VERIFIER ok=%d finish=%d\n", (int)sok, (int)fin);
    }
  }
  return 0;
}
