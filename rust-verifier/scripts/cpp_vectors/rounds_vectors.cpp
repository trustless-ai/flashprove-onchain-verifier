// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for blocks/chain/{public,rounds}.h: a hand-built plan, a Binder's two lists and their
// digest, a proof made with ProverRounds and read back with VerifierRounds. Build with
// -DBLK_FIELD=2.

#define BLK_PLANS_BY_HAND_FOR_A_TEST

#include "chain/rounds.h"
#include "hash/hash.h"
#include "iop/message.h"
#include "numbers/plan.h"

#include <cstdio>
#include <string>
#include <vector>

using namespace blk;

namespace {
void phex(const std::vector<u8> &b) {
  if (b.empty()) std::printf("-");
  for (u8 x : b) std::printf("%02x", x);
}
void pd(const char *name, const Digest &d) {
  std::printf("%s=", name);
  for (int i = 0; i < 8; i++) std::printf("%08x", d.w[i]);
}
void pv(const E &x) {
  std::printf("%016llx,%016llx,%016llx", (unsigned long long)x.c[0].v, (unsigned long long)x.c[1].v,
              (unsigned long long)x.c[2].v);
}
E e_from(u64 x) { return E{{F{x}, F{x + 1}, F{x + 2}}}; }
void set_draws(PlanRound &r, u64 elements, u64 nonzero) { r.draw_E = elements, r.draw_nonzero = nonzero; }
const u64 LABEL = 7;
Digest files() {
  Digest d{};
  d.w[0] = 0xC0F1;
  return d;
}
void bind(Binder &b) {
  b.configuration(files());
  b.parameter("a", (u64)42);
  b.statement("claim", (u64)7);
}
} // namespace

int main() {
  Setting set = setting_goldilocks();
  set.set_work(ErrorKind::QUERY, Scope::REQUEST, 2);
  Plan plan(set);
  plan.send_scalars("m0", 1);
  plan.close_none("empty");
  plan.send_scalars("m1", 2);
  set_draws(plan.close("alg", RoundKind::ALGEBRAIC, ErrorKind::FIELD, Bound((u64)0), Priced::NOTHING), 2, 2);
  set_draws(plan.close("seed", RoundKind::SEED, ErrorKind::SAMPLE, Bound((u64)0), Priced::NOTHING), 4, 1);
  plan.send_answers("answers", 2);
  plan.send_scalars("sum", 1);
  plan.close("eps", RoundKind::EPSILON, ErrorKind::FIELD, Bound((u64)0), Priced::NOTHING).draw_E = 1;
  plan.send_scalars("m2", 1);
  plan.close("bits", RoundKind::BITS, ErrorKind::SMALL, Bound((u64)0), Priced::ON_THE_CALLERS_WORD).draw_trits = 70;
  plan.send_scalars("m3", 1);
  {
    PlanRound &r = plan.close("pos", RoundKind::POSITIONS, ErrorKind::QUERY, Bound((u64)0), Priced::ON_THE_CALLERS_WORD);
    r.draw_positions = 3;
    r.log_n = 4;
    r.draw_E = 1;
  }
  plan.send_scalars("m4", 1);
  plan.close_none("last");
  plan.close("seal", RoundKind::SEAL, ErrorKind::ZERO, Bound((u64)0), Priced::NOTHING);
  const Planned q = plan.finish();
  std::printf("PLAN holds=%d rounds=%zu\n", (int)q->holds(), q->rounds_.size());
  std::printf("SET salt=%u nonce=%u position=%u samples=%u saved=%u target=%u\n", q->set.salt_bytes,
              q->set.nonce_bytes, q->set.position_bytes, q->set.samples, (unsigned)q->set.saved_coefficient,
              q->set.target);
  for (size_t i = 0; i < q->rounds_.size(); i++) {
    const PlanRound &r = q->rounds_[i];
    std::printf("ROUND i=%zu name=%s kind=%u work=%u msg=%llu roots=%u answers=%u draw_e=%llu nz=%llu draw_pos=%llu log_n=%u trits=%llu rows=%llu first_list=%llu combos=%llu sharing=%llu\n",
                i, r.name.c_str(), (unsigned)r.kind, r.work_bits, (unsigned long long)r.message_bytes, r.roots,
                r.answers, (unsigned long long)r.draw_E, (unsigned long long)r.draw_nonzero,
                (unsigned long long)r.draw_positions, r.log_n, (unsigned long long)r.draw_trits,
                (unsigned long long)r.rows, (unsigned long long)r.first_list,
                (unsigned long long)r.combinations, (unsigned long long)r.sharing);
  }

  // The Binder's lists and their digest, before any channel closes it.
  {
    Binder b(LABEL, q);
    bind(b);
    std::printf("BIND label=%llu ", (unsigned long long)LABEL);
    pd("config", files());
    std::printf(" pbytes=");
    phex(b.parameter_bytes());
    std::printf(" sbytes=");
    phex(b.statement_bytes());
    pd(" pdigest", b.parameters_digest());
    std::printf("\n");
  }

  Digest salt{};
  salt.w[0] = 0x5A17;
  Writer proof;
  {
    Binder b(LABEL, q);
    bind(b);
    ProverRounds ch(b, salt, proof);
    ch.send(e_from(1));
    ch.close_empty("empty");
    ch.send(e_from(10));
    ch.send(e_from(20));
    {
      AlgebraicDraw d = ch.close_algebraic("alg");
      const E a = d.draw_nonzero();
      const E c = d.draw_nonzero();
      std::printf("DRAW_ALG i=0 ");
      pv(a);
      std::printf(" i=1 ");
      pv(c);
      std::printf("\n");
    }
    const SampleSeed seed = ch.close_seed("seed").seed(3, 2);
    std::printf("SEED z=");
    for (size_t i = 0; i < seed.z.size(); i++) {
      if (i) std::printf(";");
      pv(seed.z[i]);
    }
    std::printf(" beta=");
    pv(seed.beta);
    std::printf("\n");
    ch.send_answer(e_from(30));
    ch.send_answer(e_from(40));
    ch.send_hiding_sum(e_from(50));
    const E eps = ch.close_epsilon("eps");
    std::printf("EPS ");
    pv(eps);
    std::printf("\n");
    ch.send(e_from(60));
    {
      BitsDraw d = ch.close_bits("bits");
      const std::vector<signed char> t = d.trits(70);
      std::printf("TRITS n=%zu v=", t.size());
      for (size_t i = 0; i < t.size(); i++) std::printf("%s%d", i ? "," : "", (int)t[i]);
      std::printf("\n");
    }
    ch.send(e_from(70));
    {
      PositionsDraw d = ch.close_positions("pos");
      const PositionList list = d.positions(4);
      const E batch = d.batching();
      std::printf("POS log_n=%u draws=", list.log_n());
      for (size_t i = 0; i < list.draws().size(); i++)
        std::printf("%s%llu", i ? "," : "", (unsigned long long)list.draws()[i]);
      std::printf(" all=");
      for (size_t i = 0; i < list.size(); i++) std::printf("%s%llu", i ? "," : "", (unsigned long long)list[i]);
      std::printf(" batch=");
      pv(batch);
      std::printf("\n");
    }
    ch.send(e_from(80));
    ch.close_empty("last");
    Sealed sealed;
    const bool sok = ch.seal("seal", sealed);
    std::printf("SEAL_PROVER ok=%d ", (int)sok);
    pd("digest", sealed.digest());
    pd(" run", ch.run());
    pd(" config", ch.configuration());
    std::printf("\n");
    ch.finish();
    std::printf("PROVER_FINISH 1\n");
  }
  std::printf("PROOF ");
  phex(proof.bytes());
  std::printf("\n");

  // The same proof through VerifierRounds.
  {
    Binder b(LABEL, q);
    bind(b);
    Reader r(proof.data(), proof.size());
    VerifierSession session;
    VerifierRounds ch(b, r, session);
    bool ok = true;
    E x;
    ok = ch.recv(x) && ok;
    ch.close_empty("empty");
    ok = ch.recv(x) && ch.recv(x) && ok;
    {
      AlgebraicDraw d = ch.close_algebraic("alg");
      const E a = d.draw_nonzero();
      const E c = d.draw_nonzero();
      std::printf("VDRAW_ALG i=0 ");
      pv(a);
      std::printf(" i=1 ");
      pv(c);
      std::printf("\n");
    }
    const SampleSeed seed = ch.close_seed("seed").seed(3, 2);
    std::printf("VSEED z=");
    for (size_t i = 0; i < seed.z.size(); i++) {
      if (i) std::printf(";");
      pv(seed.z[i]);
    }
    std::printf(" beta=");
    pv(seed.beta);
    std::printf("\n");
    ok = ch.recv_answer(x) && ch.recv_answer(x) && ok;
    ok = ch.recv_hiding_sum(x) && ok;
    const E eps = ch.close_epsilon("eps");
    std::printf("VEPS ");
    pv(eps);
    std::printf("\n");
    ok = ch.recv(x) && ok;
    {
      BitsDraw d = ch.close_bits("bits");
      const std::vector<signed char> t = d.trits(70);
      std::printf("VTRITS n=%zu v=", t.size());
      for (size_t i = 0; i < t.size(); i++) std::printf("%s%d", i ? "," : "", (int)t[i]);
      std::printf("\n");
    }
    ok = ch.recv(x) && ok;
    {
      PositionsDraw d = ch.close_positions("pos");
      const PositionList list = d.positions(4);
      const E batch = d.batching();
      std::printf("VPOS log_n=%u draws=", list.log_n());
      for (size_t i = 0; i < list.draws().size(); i++)
        std::printf("%s%llu", i ? "," : "", (unsigned long long)list.draws()[i]);
      std::printf(" all=");
      for (size_t i = 0; i < list.size(); i++) std::printf("%s%llu", i ? "," : "", (unsigned long long)list[i]);
      std::printf(" batch=");
      pv(batch);
      std::printf("\n");
    }
    ok = ch.recv(x) && ok;
    ch.close_empty("last");
    Sealed sealed;
    const bool sok = ch.seal("seal", sealed);
    std::printf("SEAL_VERIFIER ok=%d ", (int)sok);
    pd("digest", sealed.digest());
    std::printf("\n");
    const bool fin = ch.finish();
    const bool acc = session.accepted();
    std::printf("VERIFIER ok=%d finish=%d accepted=%d why=%s\n", (int)ok, (int)fin, (int)acc,
                ch.why() ? ch.why() : "-");
  }
  return 0;
}
