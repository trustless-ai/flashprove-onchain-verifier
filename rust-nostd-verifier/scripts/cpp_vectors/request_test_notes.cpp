// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Diagnostic only, S3: dumps the notes (`VerifierContext::note`, blocks/iop/context.h) of every
// proximity test that fails, so a failing BASE can be compared with the Rust port's values.
//
// It includes the checkout's unmodified verifier/src/cp_verify.cpp (with `main` renamed, as the
// other tools here do). Two function-like macros are defined after the headers that must not see
// them: `iopp_verify` (after blocks/iop/iopp.h defines it, before the headers that call it) and
// `doorH` (before vf_attention_check.h; that one is only needed to keep the include order the same
// as attention_u3_row.cpp's). The wrappers forward to the real functions and only add diagnostics.
//
// Build, from the repository root:
//   clang++ -O2 -std=c++17 -pthread -Iverifier/src -Iblocks -Iprover -DBLK_FIELD=2 \
//     -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
//     -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
//     -o /tmp/request_test_notes \
//     rust-nostd-verifier/scripts/cpp_vectors/request_test_notes.cpp
// Run with CPDUMP_FILE naming the output; notes are appended on each failed proximity test.

#include "iop/base_case.h"

#include <cstdio>
#include <unistd.h>
#include <cstdlib>
#include <string>
#include <utility>
#include <vector>

static unsigned long long cpvals_hash(const blk::Tensor &v) {
  unsigned long long h = 0xcbf29ce484222325ull;
  const size_t n = size_t(1) << v.dense_vars.size();
  for (size_t i = 0; i < n && v.values && v.first + i < v.values->size(); i++) {
    const blk::E &x = (*v.values)[v.first + i];
    for (int k = 0; k < 3; k++) { h ^= (unsigned long long)x.c[k].v; h *= 0x100000001b3ull; }
  }
  return h;
}
static void cpvals_head(char *dst, size_t cap, const blk::Tensor &v) {
  size_t at = 0;
  const size_t n = size_t(1) << v.dense_vars.size();
  for (size_t i = 0; i < 4 && v.values && v.first + i < v.values->size(); i++) {
    const blk::E &x = (*v.values)[v.first + i];
    at += (size_t)std::snprintf(dst + at, cap - at, "%016llx,%016llx,%016llx ", (unsigned long long)x.c[0].v,
                                (unsigned long long)x.c[1].v, (unsigned long long)x.c[2].v);
  }
  (void)n;
}


// Dumps the single rows that the BASE linear check sees, so the Rust port's rows can be compared.
static void cpdumpSingleRows(blk::VerifierContext &V, const blk::SingleRows &S) {
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  FILE *f = std::fopen(path, "a");
  if (!f) return;
  static int n = 0;
  const blk::Code &code = V.st.codes().base[S.code];
  std::fprintf(f, "BASE%d code=%u ell=%llu mask_code=%u masks=%u target=%016llx %016llx %016llx\n",
               n++, (unsigned)S.code, (unsigned long long)code.ell, (unsigned)S.mask_code,
               (unsigned)S.masks, (unsigned long long)S.target.c[0].v,
               (unsigned long long)S.target.c[1].v, (unsigned long long)S.target.c[2].v);
  const std::vector<blk::E> mf = blk::single_rows_main_form(S, code.ell);
  std::fprintf(f, "MF %zu", mf.size());
  for (const auto &x : mf)
    std::fprintf(f, " %016llx,%016llx,%016llx", (unsigned long long)x.c[0].v,
                 (unsigned long long)x.c[1].v, (unsigned long long)x.c[2].v);
  std::fprintf(f, "\n");
  for (size_t j = 0; j < S.d.size(); j++) {
    std::fprintf(f, "D%zu %zu", j, S.d[j].size());
    for (const auto &x : S.d[j])
      std::fprintf(f, " %016llx,%016llx,%016llx", (unsigned long long)x.c[0].v,
                   (unsigned long long)x.c[1].v, (unsigned long long)x.c[2].v);
    std::fprintf(f, "\n");
  }
  // The structure of the folded coefficient form `S.c`.
  {
    const blk::Form &C = S.c;
    std::fprintf(f, "FORM tensors=%zu entries=%zu frozen=%zu\n", C.tensors.size(), C.entries.size(),
                 C.frozen.size());
    for (size_t t = 0; t < C.tensors.size(); t++) {
      const blk::Tensor &v = C.tensors[t];
      std::fprintf(f, "T%zu vars=%u pmask=%llx pval=%llx scalar=%016llx,%016llx,%016llx first=%llu dvar=[",
                   t, v.vars(), (unsigned long long)v.pick_mask(), (unsigned long long)v.pick_value(),
                   (unsigned long long)v.scalar.c[0].v, (unsigned long long)v.scalar.c[1].v,
                   (unsigned long long)v.scalar.c[2].v, (unsigned long long)v.first);
      for (size_t q = 0; q < v.dense_vars.size(); q++)
        std::fprintf(f, "%s%u", q ? "," : "", v.dense_vars[q]);
      std::fprintf(f, "] nvals=%zu at0=%016llx at1=%016llx pairs=", v.values ? v.values->size() : 0, (unsigned long long)v.at(0).c[0].v, (unsigned long long)v.at(1).c[0].v);
      if (v.values) { char hd[256] = {0}; cpvals_head(hd, sizeof hd, v); std::fprintf(f, "vhash=%016llx vhead=%s", cpvals_hash(v), hd); }
      if (v.values && v.dense_vars.size() >= 9) {
        std::fprintf(f, " full=");
        const size_t n = size_t(1) << v.dense_vars.size();
        for (size_t i = 0; i < n && v.first + i < v.values->size(); i++) {
          const blk::E &x = (*v.values)[v.first + i];
          std::fprintf(f, "%016llx,%016llx,%016llx;", (unsigned long long)x.c[0].v,
                       (unsigned long long)x.c[1].v, (unsigned long long)x.c[2].v);
        }
      }
      for (unsigned q = 0; q < v.vars(); q++)
        std::fprintf(f, "(%016llx,%016llx,%016llx:%016llx,%016llx,%016llx)", (unsigned long long)v.lo(q).c[0].v,
                     (unsigned long long)v.lo(q).c[1].v, (unsigned long long)v.lo(q).c[2].v,
                     (unsigned long long)v.hi(q).c[0].v, (unsigned long long)v.hi(q).c[1].v,
                     (unsigned long long)v.hi(q).c[2].v);
      std::fprintf(f, "\n");
    }
    for (size_t t = 0; t < C.entries.size() && t < 64; t++)
      std::fprintf(f, "E%zu %llu %016llx,%016llx,%016llx\n", t,
                   (unsigned long long)C.entries[t].first,
                   (unsigned long long)C.entries[t].second.c[0].v,
                   (unsigned long long)C.entries[t].second.c[1].v,
                   (unsigned long long)C.entries[t].second.c[2].v);
    for (size_t t = 0; t < C.frozen.size(); t++) {
      const blk::FrozenPart &p = C.frozen[t];
      std::fprintf(f, "P%zu vars=%u scale=%016llx,%016llx,%016llx cmask=%llx cval=%llx inner=%zu,%zu,%zu\n",
                   t, p.vars, (unsigned long long)p.scale.c[0].v, (unsigned long long)p.scale.c[1].v,
                   (unsigned long long)p.scale.c[2].v, (unsigned long long)p.choice_mask,
                   (unsigned long long)p.choice_value, p.form->tensors.size(), p.form->entries.size(),
                   p.form->frozen.size());
      const blk::Form &I = *p.form;
      for (size_t u = 0; u < I.tensors.size(); u++) {
        const blk::Tensor &v = I.tensors[u];
        std::fprintf(f, "IT%zu vars=%u pmask=%llx pval=%llx scalar=%016llx,%016llx,%016llx first=%llu dvar=[",
                     u, v.vars(), (unsigned long long)v.pick_mask(), (unsigned long long)v.pick_value(),
                     (unsigned long long)v.scalar.c[0].v, (unsigned long long)v.scalar.c[1].v,
                     (unsigned long long)v.scalar.c[2].v, (unsigned long long)v.first);
        for (size_t q = 0; q < v.dense_vars.size(); q++)
          std::fprintf(f, "%s%u", q ? "," : "", v.dense_vars[q]);
        std::fprintf(f, "] nvals=%zu at0=%016llx at1=%016llx pairs=", v.values ? v.values->size() : 0, (unsigned long long)v.at(0).c[0].v, (unsigned long long)v.at(1).c[0].v);
      if (v.values) { char hd[256] = {0}; cpvals_head(hd, sizeof hd, v); std::fprintf(f, "vhash=%016llx vhead=%s", cpvals_hash(v), hd); }
      if (v.values && v.dense_vars.size() >= 9) {
        std::fprintf(f, " full=");
        const size_t n = size_t(1) << v.dense_vars.size();
        for (size_t i = 0; i < n && v.first + i < v.values->size(); i++) {
          const blk::E &x = (*v.values)[v.first + i];
          std::fprintf(f, "%016llx,%016llx,%016llx;", (unsigned long long)x.c[0].v,
                       (unsigned long long)x.c[1].v, (unsigned long long)x.c[2].v);
        }
      }
        for (unsigned q = 0; q < v.vars(); q++)
          std::fprintf(f, "(%016llx,%016llx,%016llx:%016llx,%016llx,%016llx)", (unsigned long long)v.lo(q).c[0].v,
                       (unsigned long long)v.lo(q).c[1].v, (unsigned long long)v.lo(q).c[2].v,
                       (unsigned long long)v.hi(q).c[0].v, (unsigned long long)v.hi(q).c[1].v,
                       (unsigned long long)v.hi(q).c[2].v);
        std::fprintf(f, "\n");
      }
      for (size_t u = 0; u < I.entries.size() && u < 64; u++)
        std::fprintf(f, "IE%zu %llu %016llx,%016llx,%016llx\n", u, (unsigned long long)I.entries[u].first,
                     (unsigned long long)I.entries[u].second.c[0].v,
                     (unsigned long long)I.entries[u].second.c[1].v,
                     (unsigned long long)I.entries[u].second.c[2].v);
    }
  }
  std::fclose(f);
}


static bool cp_base(blk::VerifierContext &V, const blk::SingleRows &S, blk::BaseMask mask,
                    unsigned leafClass) {
  cpdumpSingleRows(V, S);
  return (blk::base_verify)(V, S, std::move(mask), leafClass);
}
#define base_verify(V, S, mask, leaf) cp_base((V), (S), (mask), (leaf))

#include "iop/iopp.h"

static std::vector<std::pair<std::string, blk::E>> g_notes;

static void cpdumpNotes(const char *tag) {
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  FILE *f = std::fopen(path, "a");
  if (!f) return;
  std::fprintf(f, "NOTES %s n=%zu\n", tag, g_notes.size());
  for (const auto &x : g_notes) {
    std::fprintf(f, "%s %016llx %016llx %016llx\n", x.first.c_str(),
                 (unsigned long long)x.second.c[0].v, (unsigned long long)x.second.c[1].v,
                 (unsigned long long)x.second.c[2].v);
  }
  std::fclose(f);
}

template <class... Args> static bool cp_iopp(blk::VerifierContext &V, Args &&...a) {
  auto *save = V.notes;
  V.notes = &g_notes;
  const size_t start = g_notes.size();
  const bool ok = (blk::iopp_verify)(V, std::forward<Args>(a)...);
  V.notes = save;
  std::vector<std::pair<std::string, blk::E>> kept(g_notes.begin() + (long)start, g_notes.end());
  g_notes = std::move(kept);
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  if (FILE *f = std::fopen(path, "a")) {
    static int n = 0;
    std::fprintf(f, "TEST %d ok=%d n=%zu\n", n++, ok ? 1 : 0, g_notes.size());
    for (const auto &x : g_notes) {
      if (x.first.rfind("BASE:", 0) != 0 && x.first.rfind("FOLD: target", 0) != 0 &&
          x.first.rfind("CS: target", 0) != 0)
        continue;
      std::fprintf(f, "%s %016llx %016llx %016llx\n", x.first.c_str(),
                   (unsigned long long)x.second.c[0].v, (unsigned long long)x.second.c[1].v,
                   (unsigned long long)x.second.c[2].v);
    }
    std::fclose(f);
  }
  return ok;
}
#define iopp_verify(V, ...) cp_iopp((V), __VA_ARGS__)

// Everything cp_verify.cpp includes except vf_attention_check.h; the two macros are in force.
#include "vf_smallness_matrices.h"
#include "vf_input_files.h"
#include "frame/heads.h"
#include "frame/parameters.h"
#include "vf_attention_shape.h"
#include "vf_subproof_engine.h"
#include "vf_smallness_test.h"
#include "vf_norm_digit_rows.h"
#include "vf_weights_layout.h"
#include "frame/check.h"
#include "frame/check_entry.h"
#include "frame/check_key.h"
#include "cp_configured.h"
#include "frame/prints.h"
#include "frame/req_frame.h"
#include "frame/wf_units.h"
#include "vf_weights_pending_claim.h"

// Dumps every pending claim's row weights, so the Rust port's can be compared.
static WsPending cp_wsPending(const WsLay &lay, const WsForkOut &o, size_t claims,
                              const blk::LinShape &S) {
  WsPending p = (wsPending)(lay, o, claims, S);
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  if (FILE *f = std::fopen(path, "a")) {
    std::fprintf(f, "WSPEND g=%zu psi=%zu", p.g.size(), p.psi.size());
    for (const blk::Tensor &t : p.g) {
      unsigned long long h = 0xcbf29ce484222325ull;
      const size_t n = size_t(1) << t.dense_vars.size();
      if (t.values)
        for (size_t i = 0; i < n && t.first + i < t.values->size(); i++) {
          const blk::E &x = (*t.values)[t.first + i];
          for (int k = 0; k < 3; k++) { h ^= (unsigned long long)x.c[k].v; h *= 0x100000001b3ull; }
        }
      std::fprintf(f, " T(vars=%u pmask=%llx pval=%llx first=%llu n=%zu hash=%016llx)", t.vars(),
                   (unsigned long long)t.pick_mask(), (unsigned long long)t.pick_value(),
                   (unsigned long long)t.first, t.values ? t.values->size() : 0, h);
    }
    std::fprintf(f, " UNITS");
    for (size_t ui = 0; ui < lay.U.size(); ui++)
      std::fprintf(f, " (%zu off=%llu rows=%llu nlw=%d ng=%zu)", ui, (unsigned long long)lay.U[ui].off,
                   (unsigned long long)lay.U[ui].rows, (int)lay.U[ui].nlw, lay.U[ui].g.size());
    std::fprintf(f, " REC");
    for (size_t ri = 0; ri < o.rec.size(); ri++)
      std::fprintf(f, " (ui=%zu ka=%016llx,%016llx,%016llx nf=%zu)", (size_t)o.rec[ri].ui,
                   (unsigned long long)o.rec[ri].ka.c[0], (unsigned long long)o.rec[ri].ka.c[1],
                   (unsigned long long)o.rec[ri].ka.c[2], o.rec[ri].f.size());
    for (size_t ri = 0; ri < o.rec.size(); ri++) {
      const WsRecClaim &c = o.rec[ri];
      const WsUnit &u = lay.U[c.ui];
      std::fprintf(f, "\nFAC%zu ui=%zu", ri, (size_t)c.ui);
      for (size_t gi = 0; gi < c.f.size() && gi < u.g.size(); gi++) {
        const WsGrp &g = u.g[gi];
        const WsRowFac &x = c.f[gi];
        std::fprintf(f, " g%zu(cls=%c r=%llu o=%llu left=%llu z=%d t=%d HV=", gi, g.cls,
                     (unsigned long long)g.R, (unsigned long long)g.o, (unsigned long long)g.left,
                     (int)g.z, (int)g.t);
        for (const Ex &e : x.HV) std::fprintf(f, "%016llx,", (unsigned long long)e.c[0]);
        std::fprintf(f, " pl=");
        for (const Ex &e : x.pl) std::fprintf(f, "%016llx,", (unsigned long long)e.c[0]);
        std::fprintf(f, " AV=");
        for (const Ex &e : x.AV) std::fprintf(f, "%016llx,", (unsigned long long)e.c[0]);
        std::fprintf(f, ")");
      }
    }
    if (!p.g.empty() && p.g[0].values) {
      const std::vector<blk::E> &vv = *p.g[0].values;
      std::fprintf(f, " BLOCKS");
      for (size_t b = 0; b * 1024 < vv.size(); b++) {
        unsigned long long h = 0xcbf29ce484222325ull;
        for (size_t i = b * 1024; i < (b + 1) * 1024 && i < vv.size(); i++) {
          const blk::E &x = vv[i];
          for (int k = 0; k < 3; k++) { h ^= (unsigned long long)x.c[k].v; h *= 0x100000001b3ull; }
        }
        std::fprintf(f, " %016llx", h);
      }
    }
    std::fprintf(f, " beta=%016llx:%016llx:%016llx target=%016llx:%016llx:%016llx\n",
                 (unsigned long long)p.beta.c[0].v, (unsigned long long)p.beta.c[1].v,
                 (unsigned long long)p.beta.c[2].v, (unsigned long long)p.target.c[0].v,
                 (unsigned long long)p.target.c[1].v, (unsigned long long)p.target.c[2].v);
    std::fclose(f);
  }
  return p;
}
#define wsPending(lay, o, claims, S) cp_wsPending((lay), (o), (claims), (S))

// TEMP: the accounting that the parent prints for the call.
namespace blk {
static void cp_pa(const Accounting &a, const char *what, bool rounds_listed = false, size_t top = 6) {
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  if (FILE *f = std::fopen(path, "a")) {
    std::fprintf(f, "PACCT pid=%d what=%s calls=%llu counted=%d planned=%llu\n", (int)getpid(), what,
                 (unsigned long long)a.calls, a.counted ? 1 : 0, (unsigned long long)a.planned_calls);
    std::fclose(f);
  }
  (print_accounting)(a, what, rounds_listed, top);
}
}  // namespace blk
#define print_accounting(...) cp_pa(__VA_ARGS__)

// TEMP: the parsed stage records.
static bool cp_acctReadH(const std::string &out, blk::Accounting &a) {
  static unsigned long long running = 0;
  const bool r = (acctReadH)(out, a);
  running += a.calls;
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  if (FILE *f = std::fopen(path, "a")) {
    std::fprintf(f, "ACCTREAD pid=%d ok=%d calls=%llu planned=%llu rounds=%llu counted=%d running=%llu\n", (int)getpid(), r ? 1 : 0,
                 (unsigned long long)a.calls, (unsigned long long)a.planned_calls, (unsigned long long)a.rounds, a.counted ? 1 : 0, running);
    std::fclose(f);
  }
  return r;
}
#define acctReadH(...) cp_acctReadH(__VA_ARGS__)

// TEMP: the final call-level counters.
namespace f2b {
static uint64_t cp_calls_total() {
  const uint64_t v = calls_total();
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  if (FILE *f = std::fopen(path, "a")) { std::fprintf(f, "CALLT pid=%d f2b=%llu\n", (int)getpid(), (unsigned long long)v); std::fclose(f); }
  return v + 12345;
}
}
namespace blk {
static u64 cp_hcc() {
  const u64 v = hash_calls_counted();
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  if (FILE *f = std::fopen(path, "a")) { std::fprintf(f, "CALLB pid=%d blk=%llu\n", (int)getpid(), (unsigned long long)v); std::fclose(f); }
  return v;
}
}
#define calls_total(...) cp_calls_total(__VA_ARGS__)
#define hash_calls_counted(...) cp_hcc(__VA_ARGS__)

// TEMP: configuration digest call sizes and counts.
namespace blk {
static Digest cp_cd(const std::vector<std::string> &files) {
  const u64 before = hash_calls_counted();
  const Digest d = (configuration_digest)(files);
  const u64 after = hash_calls_counted();
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  if (FILE *f = std::fopen(path, "a")) {
    std::fprintf(f, "CD pid=%d n=%zu", (int)getpid(), files.size());
    for (const std::string &x : files) std::fprintf(f, " %zu", x.size());
    std::fprintf(f, " delta=%llu\n", (unsigned long long)(after - before));
    std::fclose(f);
  }
  return d;
}
}  // namespace blk
#define configuration_digest(...) cp_cd(__VA_ARGS__)

// TEMP: per-call hash counts of the earlier hash.
static void cp_ehd(u32 out[], u32 num, const u32 *w, u64 L, u64 stride = 1) {
  const u64 before = f2b::calls_total();
  (earlier_hash_h_digest)(out, num, w, L, stride);
  const u64 after = f2b::calls_total();
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  if (FILE *f = std::fopen(path, "a")) {
    std::fprintf(f, "EHD pid=%d num=%u L=%llu stride=%llu delta=%llu\n", (int)getpid(), (unsigned)num,
                 (unsigned long long)L, (unsigned long long)stride,
                 (unsigned long long)(after - before));
    std::fclose(f);
  }
}
#define earlier_hash_h_digest(...) cp_ehd(__VA_ARGS__)

// TEMP: hash-call counters just before the commitment ID is computed.
namespace blk {
static Digest cp_published_id2(const Configured &c, const IndexReader &first_table) {
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_notes.txt";
  if (FILE *f = std::fopen(path, "a")) {
    std::fprintf(f, "CPPID pid=%d f2b=%llu blk=%llu\n", (int)getpid(), (unsigned long long)f2b::calls_total(),
                 (unsigned long long)blk::hash_calls_counted());
    std::fclose(f);
  }
  const Digest d = (published_id)(c, first_table);
  if (FILE *f = std::fopen(path, "a")) {
    std::fprintf(f, "CPPID-AFTER f2b=%llu blk=%llu\n", (unsigned long long)f2b::calls_total(),
                 (unsigned long long)blk::hash_calls_counted());
    std::fclose(f);
  }
  return d;
}
}  // namespace blk
#define published_id(...) cp_published_id2(__VA_ARGS__)

static void cpDoorForward(HFork &F, Tail2 &T, Tr &tr, u64 equationsLaid) {
  (doorH)(F, T, tr, equationsLaid);
}
#define doorH(F, T, tr, e) (cpDoorForward((F), (T), (tr), (e)))

#define main cp_verify_original_main
#include "../../verifier/src/cp_verify.cpp"
#undef main

int main(int argc, char **argv) { return cp_verify_original_main(argc, argv); }
