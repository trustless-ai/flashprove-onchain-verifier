// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for the verifier's request frame: `ReqFrame`/`ReqVerifier` (blocks/iop/req.h),
// `ReqRows` (blocks/iop/req_rows.h) and `ChainCheck` (verifier/src/vf_request_chain.h), on the
// toy requests of blocks/iop/tests/req_rows_cases.h. For each case the tool dumps the shape, the
// layout and the plan, the proof (as bytes) and the verdicts of the honest run and of runs that
// must be rejected; then a battery of malformed shapes and layouts with the fault names that
// req_fault() and req_layout_fault() return.
//
// Usage: req_chain_vectors > req_chain_vectors.txt

#include "vf_request_chain.h"

#include "iop/tests/req_rows_cases.h"

#include <algorithm>
#include <cinttypes>
#include <cstdio>
#include <string>
#include <vector>

using namespace blk;

static void phex(const std::vector<u8> &b) {
  if (b.empty()) {
    std::printf("-");
    return;
  }
  for (u8 x : b) std::printf("%02x", x);
}
static void pe(const E &x) {
  std::printf("%016" PRIx64 ",%016" PRIx64 ",%016" PRIx64, (u64)x.c[0].v, (u64)x.c[1].v, (u64)x.c[2].v);
}
static void pweights(const char *name, const IndexWeights &w) {
  std::printf(" %s=", name);
  if (w.values) {
    std::printf("w:%zu", w.values->size());
    for (const E &x : *w.values) {
      std::printf(",");
      pe(x);
    }
    return;
  }
  std::printf("e:%zu", w.lo.size());
  for (size_t i = 0; i < w.lo.size(); i++) {
    std::printf(",");
    pe(w.lo[i]);
    std::printf(",");
    pe(w.hi[i]);
  }
}
static void pd(const char *name, const Digest &d) {
  std::printf("%s=", name);
  for (int i = 0; i < 8; i++) std::printf("%08x", d.w[i]);
}
static u64 hash_bytes(const std::vector<u8> &b) {
  u64 h = 1469598103934665603ull;  // FNV-1a, for a sanity print alone
  for (u8 x : b) {
    h ^= x;
    h *= 1099511628211ull;
  }
  return h;
}

// The hook of verifier/tests/req_chain_test.cpp: reads the equation's value at the last commit
// point of its segment and closes with the equation built from the seed.
struct MadeUpHook : mb::LinkHook {
  const ReqWorld &w;
  const ReqLayout &layout;
  size_t link;
  u64 seed;
  bool spoil;
  E target;
  MadeUpHook(const ReqWorld &world, const ReqLayout &lay, size_t l, u64 s, bool sp)
      : w(world), layout(lay), link(l), seed(s), spoil(sp) {}
  bool run(unsigned moment, VerifierContext &V, const ReqFrame &frame, const std::vector<OracleId> &) override {
    return moment + 1 < w.shape.link[link].moments() || V.ch.recv(target);
  }
  void claim(E &t, std::vector<E> &on_masks) override {
    t = target, on_masks = rows_toy_equation(w, layout, link, seed, false).on_masks;
  }
  std::vector<ReqTerm> terms() override { return rows_toy_equation(w, layout, link, seed, spoil).terms; }
};

static bool verify_chain(const ReqWorld &w, const ReqLayout &layout, u64 seed, const std::vector<u8> &proof, bool spoil) {
  Binder binder(1, w.plan);
  const RowsPublic bound = rows_toy_bind(binder, w, layout, seed);
  Reader reader(proof.data(), proof.size());
  VerifierSession session;
  VerifierRounds channel(binder, reader, session);
  VerifierContext V(bound.codes, channel);
  std::vector<MadeUpHook> made;
  for (size_t l = 0; l < w.shape.link.size(); l++) made.emplace_back(w, channel.get(bound.layout), l, channel.get(bound.seed), spoil && l == 0);
  std::vector<mb::LinkHook *> hooks;
  for (MadeUpHook &h : made) hooks.push_back(&h);
  if (!mb::chain_verify(V, mb::ChainShape{bound.shape, bound.layout}, hooks)) return false;
  return channel.finish();
}

static bool verify_by_calls(const ReqWorld &w, const ReqLayout &layout, u64 seed, const std::vector<u8> &proof,
                            size_t no_close = ~size_t(0), size_t no_moment = ~size_t(0)) {
  Binder binder(1, w.plan);
  const RowsPublic bound = rows_toy_bind(binder, w, layout, seed);
  Reader reader(proof.data(), proof.size());
  VerifierSession session;
  VerifierRounds channel(binder, reader, session);
  VerifierContext V(bound.codes, channel);
  mb::ChainCheck check(V, mb::ChainShape{bound.shape, bound.layout});
  for (size_t l = 0; l < w.shape.link.size(); l++) {
    if (!check.first()) return false;
    for (unsigned moment = 1; moment + (l == no_moment ? 1 : 0) < w.shape.link[l].moments(); moment++)
      if (!check.later()) return false;
    if (l == no_close) continue;
    ReqEquation equation = rows_toy_equation(w, channel.get(bound.layout), l, channel.get(bound.seed), false);
    if (!V.ch.recv(equation.target) || !check.close(equation)) return false;
  }
  return check.finish() && channel.finish();
}

static std::string ident(std::string s) {
  for (char &c : s)
    if (c == ' ') c = '_';
  return s;
}

static void dump_world(const char *name, const ReqWorld &w, const ReqLayout &layout, u64 seed) {
  std::printf("CASE name=%s links=%zu seed=%" PRIu64 "\n", ident(name).c_str(), w.shape.link.size(), seed);
  std::printf("CODES base=%zu mask=%zu\n", w.codes.base.size(), w.codes.mask.size());
  for (size_t i = 0; i < w.codes.base.size(); i++)
    std::printf("CODE base i=%zu log_n=%u ell=%" PRIu64 " r=%" PRIu64 "\n", i, w.codes.base[i].log_n, (u64)w.codes.base[i].ell,
                (u64)w.codes.base[i].r);
  for (size_t i = 0; i < w.codes.mask.size(); i++)
    std::printf("CODE mask i=%zu log_n=%u ell=%" PRIu64 " r=%" PRIu64 "\n", i, w.codes.mask[i].log_n, (u64)w.codes.mask[i].ell,
                (u64)w.codes.mask[i].r);
  std::printf("SHAPE code=%u mask_code=%u answers=%u masks_ride=%d\n", w.shape.code, w.shape.mask_code, w.shape.answers,
              (int)w.shape.choice.masks_ride);
  for (size_t l = 0; l < w.shape.link.size(); l++) {
    const ReqLink &L = w.shape.link[l];
    std::printf("LINK l=%zu name=%s plain=%u\n", l, ident(L.name).c_str(), L.plain);
    for (size_t m = 0; m < L.messages.size(); m++) {
      const ReqMessage &M = L.messages[m];
      std::printf("MSG l=%zu m=%zu name=%s code=%u main_rows=%zu main_deg=%u mask_rows=%zu mask_code=%u answers=%u leaf=%u moment=%u life=%u\n",
                  l, m, M.shape.name.c_str(), M.shape.code, M.shape.main_rows, M.shape.main_deg, M.shape.mask_rows,
                  M.shape.mask_code, M.shape.answers, M.leaf_class, M.moment, M.life);
    }
  }
  for (size_t i = 0; i < w.shape.at_start.size(); i++) {
    const OracleShape &o = w.shape.at_start[i].shape;
    std::printf("NOTICE i=%zu name=%s code=%u main_rows=%zu main_deg=%u mask_rows=%zu mask_code=%u answers=%u leaf=%u\n", i,
                o.name.c_str(), o.code, o.main_rows, o.main_deg, o.mask_rows, o.mask_code, o.answers, w.shape.at_start[i].leaf_class);
  }
  for (size_t i = 0; i < w.shape.last.size(); i++)
    std::printf("STAGE i=%zu code=%u mask_code=%u k=%u h=%u\n", i, w.shape.last[i].code, w.shape.last[i].mask_code,
                w.shape.last[i].k, w.shape.last[i].h);
  for (size_t l = 0; l < layout.link.size(); l++) {
    const std::vector<ReqArray> &arrays = layout.link[l];
    for (size_t a = 0; a < arrays.size(); a++) {
      const ReqArray &A = arrays[a];
      std::printf("LAYOUT l=%zu a=%zu name=%s message=%zu size_i=%" PRIu64 " size_c=%" PRIu64 "\n", l, a, A.name.c_str(),
                  A.message, A.laid.size_i, A.laid.size_c);
      for (size_t b = 0; b < A.laid.blocks.size(); b++) {
        const LaidBlock &B = A.laid.blocks[b];
        std::printf("BLOCK l=%zu a=%zu b=%zu fi=%" PRIu64 " bi=%u fc=%" PRIu64 " bc=%u fr=%" PRIu64 " rb=%u fp=%" PRIu64 " pb=%u low=%d\n",
                    l, a, b, B.first_i, B.bits_i, B.first_c, B.bits_c, B.first_row, B.row_bits, B.first_place, B.place_bits,
                    (int)B.i_is_low);
      }
    }
  }
  for (size_t l = 0; l < w.shape.link.size(); l++) {
    const ReqEquation eq = rows_toy_equation(w, layout, l, seed, false);
    for (size_t t = 0; t < eq.terms.size(); t++) {
      const ReqTerm &T = eq.terms[t];
      std::printf("TERM l=%zu t=%zu born=%zu array=%s scale=", l, t, T.born, T.array.c_str());
      pe(T.scale);
      pweights("rows", T.on_rows);
      pweights("cols", T.on_columns);
      std::printf("\n");
    }
    std::printf("MASKS l=%zu n=%zu", l, eq.on_masks.size());
    for (const E &x : eq.on_masks) {
      std::printf(",");
      pe(x);
    }
    std::printf("\n");
  }
  std::printf("PLAN rounds=%zu\n", w.plan->rounds_.size());
  const Setting &set = w.plan->set;
  std::printf("SET salt=%u nonce=%u position=%u samples=%u saved=%u target=%u\n", set.salt_bytes, set.nonce_bytes,
              set.position_bytes, set.samples, (unsigned)set.saved_coefficient, set.target);
  for (size_t i = 0; i < w.plan->rounds_.size(); i++) {
    const PlanRound &r = w.plan->rounds_[i];
    std::printf("ROUND i=%zu kind=%u work=%u count=%" PRIu64 " msg=%" PRIu64 " roots=%u answers=%u draw_e=%" PRIu64
                " nz=%" PRIu64 " draw_pos=%" PRIu64 " log_n=%u trits=%" PRIu64 " rows=%" PRIu64 " first_list=%" PRIu64
                " combos=%" PRIu64 " sharing=%" PRIu64 " gsaid=%d gk=%u gh=%u gslots=%" PRIu64
                " gml=%u gme=%" PRIu64 " gmr=%" PRIu64 " gzl=%u gze=%" PRIu64 " gzr=%" PRIu64 " name=%s\n",
                i, (unsigned)r.kind, r.work_bits, r.count, (u64)r.message_bytes, r.roots, r.answers,
                r.draw_E, r.draw_nonzero, r.draw_positions, r.log_n, r.draw_trits, r.rows, r.first_list, r.combinations, r.sharing,
                (int)r.group.said, r.group.k, r.group.h, r.group.slots, r.group.main.log_n, (u64)r.group.main.ell,
                (u64)r.group.main.r, r.group.mask.log_n, (u64)r.group.mask.ell, (u64)r.group.mask.r, r.name.c_str());
  }
}

// One mutation of the shape or the layout, and the name that the check returns for it. The
// mutations are applied again by the Rust replay, by key.
static void fault_shape(const char *key, const ReqWorld &w) {
  const char *n = req_fault(w.codes, w.shape);
  std::printf("FAULT key=%s name=%s\n", key, n ? n : "-");
}
static void fault_layout(const char *key, const ReqWorld &w, const ReqLayout &lay) {
  const char *n = req_layout_fault(w.codes, w.shape, lay);
  std::printf("FAULT key=%s name=%s\n", key, n ? n : "-");
}
static void dump_faults(const ReqWorld &w0, const ReqLayout &lay0) {
  ReqWorld w = w0;
  ReqLayout lay = lay0;
  auto reset = [&]() { w = w0, lay = lay0; };
  const size_t links = w.shape.link.size();

  reset(), w.shape.answers = 0, fault_shape("answers_zero", w);
  reset(), w.shape.link[0].messages[0].shape.main_rows = 0, w.shape.link[0].messages[0].shape.mask_rows = 0,
      fault_shape("message_no_rows", w);
  reset(), w.shape.link[0].messages[0].shape.main_rows = REQ_MOST_ROWS + 1, fault_shape("message_too_many_rows", w);
  reset(), w.shape.link[0].messages[0].shape.main_deg = 2, fault_shape("message_bad_degree", w);
  reset(), w.shape.link[0].messages[0].life = 1, fault_shape("kept_with_mask", w);
  reset(), w.shape.link[0].messages.push_back(w.shape.link[0].messages[1]),
      w.shape.link[0].messages.back().moment = 9, fault_shape("moment_gap", w);
  reset(), w.shape.link[0].messages[1].shape.answers = 2, fault_shape("answers_mismatch", w);
  reset(), w.shape.link[0].messages[0].shape.code = 1, fault_shape("main_code_mismatch", w);
  reset(), w.shape.link[0].messages[0].shape.mask_code = 1, fault_shape("mask_code_mismatch", w);
  reset(), w.shape.link[0].messages[0].shape.mask_rows = 0, w.shape.link[0].messages[0].life = (unsigned)links,
      fault_shape("kept_beyond_last", w);
  reset();
  w.shape.link[0].messages.erase(std::remove_if(w.shape.link[0].messages.begin(), w.shape.link[0].messages.end(),
                                                [](const ReqMessage &m) { return m.moment != 0; }),
                                 w.shape.link[0].messages.end());
  for (ReqMessage &m : w.shape.link[0].messages) m.shape.mask_rows = 0, m.life = 1;
  fault_shape("first_link_no_fold", w);
  reset();
  {
    OracleNotice n;
    n.shape.name = "rider", n.shape.main_rows = 1, n.shape.mask_rows = 1, n.shape.mask_code = 0, n.shape.answers = w.shape.answers;
    n.leaf_class = 1;
    w.shape.at_start.push_back(n);
  }
  fault_shape("at_start_main_rows", w);
  reset();
  {
    OracleNotice n;
    n.shape.name = "rider", n.shape.mask_rows = 1, n.shape.mask_code = 0, n.shape.answers = 99;
    n.leaf_class = 1;
    w.shape.at_start.push_back(n);
  }
  fault_shape("at_start_answers", w);
  reset();
  {
    OracleNotice n;
    n.shape.name = "rider", n.shape.mask_rows = 1, n.shape.mask_code = 0, n.shape.answers = w.shape.answers;
    n.leaf_class = 0;
    w.shape.at_start.push_back(n);
  }
  fault_shape("at_start_class", w);
  reset(), w.shape.last.resize(1), fault_shape("last_too_few", w);
  reset(), w.shape.last[0].k += 1, fault_shape("last_group", w);
  reset();
  {
    const CodeId bad = (CodeId)w.codes.base.size();
    w.shape.code = bad;
    for (ReqLink &L : w.shape.link)
      for (ReqMessage &m : L.messages)
        if (m.shape.main_rows) m.shape.code = bad;
    w.shape.last[0].code = bad;
  }
  fault_shape("code_missing", w);
  reset();
  {
    const unsigned many = (unsigned)w.codes.base[0].ell;
    w.shape.answers = many;
    for (ReqLink &L : w.shape.link)
      for (ReqMessage &m : L.messages) m.shape.answers = many;
  }
  fault_shape("answers_too_many", w);

  reset(), lay.link.pop_back(), fault_layout("layout_link_count", w, lay);
  reset(), lay.link[0][0].message = 99, fault_layout("layout_message_missing", w, lay);
  reset(), lay.link[0][1].name = lay.link[0][0].name, fault_layout("layout_duplicate_name", w, lay);
  reset(), lay.link[0][0].laid.blocks[0].first_i = 1, fault_layout("layout_bad_block", w, lay);
  reset();
  {
    // A one-row array in row 3: inside the table (4 rows) but not in the message's sent rows (3).
    LaidBlock b;
    b.first_row = 3, b.row_bits = 0, b.place_bits = 0, b.first_place = 0;
    lay.link[0].push_back(ReqArray{"U", 0, LaidMatrix{1, 1, {b}}});
  }
  fault_layout("layout_row_unsent", w, lay);
  reset();
  {
    // A one-entry block on the first pad place of a message's sample covers it.
    size_t m = 0;
    while (m + 1 < w.shape.link[0].messages.size() && w.shape.link[0].messages[m].shape.mask_rows) m++;
    const OracleShape &o = w.shape.link[0].messages[m].shape;
    std::vector<PadPlace> pads = Send::pad(w.codes, o);
    bool placed = false;
    for (const PadPlace &p : pads) {
      if (p.part != Part::MAIN) continue;
      const unsigned row_bits = ceil_log2(o.main_rows);
      LaidBlock b;
      b.first_row = p.index & ((u64(1) << row_bits) - 1), b.row_bits = 0;
      b.first_place = p.index >> row_bits, b.place_bits = 0;
      lay.link[0].push_back(ReqArray{"P", m, LaidMatrix{1, 1, {b}}});
      placed = true;
      break;
    }
    if (placed)
      fault_layout("layout_pad", w, lay);
    else
      std::printf("FAULT key=layout_pad name=-\n");
  }
}

int main() {
  const std::vector<ReqCase> cases = rows_toy_cases();
  for (const ReqCase &t : cases) {
    const ReqWorld w = req_toy_world(t, 1);
    const ReqLayout layout = rows_toy_layout(w);
    const u64 seed = 800;
    EngineCpu engine, again;
    const std::vector<u8> proof = rows_prove(w, layout, seed, E::zero(), engine);
    const std::vector<u8> false_proof = rows_prove(w, layout, seed, E::one(), again);
    dump_world(t.name, w, layout, seed);
    std::printf("PROOF len=%zu hash=%016" PRIx64 " trees=%zu\n", proof.size(), hash_bytes(proof), (size_t)0);
    std::printf("PROOF_HEX ");
    phex(proof);
    std::printf("\n");
    std::printf("FALSEPROOF len=%zu hash=%016" PRIx64 "\n", false_proof.size(), hash_bytes(false_proof));
    std::printf("FALSEPROOF_HEX ");
    phex(false_proof);
    std::printf("\n");
    std::printf("VERDICT honest_chain=%d honest_calls=%d spoil=%d false_chain=%d false_calls=%d\n",
                (int)verify_chain(w, layout, seed, proof, false), (int)verify_by_calls(w, layout, seed, proof),
                (int)verify_chain(w, layout, seed, proof, true), (int)verify_chain(w, layout, seed, false_proof, false),
                (int)verify_by_calls(w, layout, seed, false_proof));
    for (size_t l = 0; l < w.shape.link.size(); l++)
      std::printf("NOCLOSE l=%zu ok=%d\nNOMOMENT l=%zu ok=%d\n", l, (int)verify_by_calls(w, layout, seed, proof, l),
                  l, (int)verify_by_calls(w, layout, seed, proof, ~size_t(0), l));
    std::printf("ENDCASE\n");
  }
  {
    const ReqWorld w = req_toy_world(cases[0], 1);
    const ReqLayout layout = rows_toy_layout(w);
    dump_faults(w, layout);
  }
  return 0;
}
