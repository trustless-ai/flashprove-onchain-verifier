// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Diagnostic only, S3: dumps the U3 column weights (HRow::L of tree 0) of every attention
// sub-proof at its door equation, so they can be compared with the Rust port's row.
//
// It includes the checkout's unmodified verifier/src/cp_verify.cpp (as the other tools here do,
// with `main` renamed) and wraps the segment's doorH() with a macro defined after
// vf_subproof_segment.h is included: the call the attention sub-proof makes in
// vf_attention_check.h then runs cpdumpDoor(), which writes the row and forwards to the real
// doorH(). The layers and head sub-proofs also pass through the wrapper and are not dumped (their
// tree list is not the attention's).
//
// Build, from the repository root:
//   clang++ -O2 -std=c++17 -pthread -Iverifier/src -Iblocks -Iprover -DBLK_FIELD=2 \
//     -DBLK_COUNT_HASH_CALLS=1 -DSERVING_BUILD=1 -DDIGEST_WORDS=8 \
//     -DVF_SOURCE_DIGEST='"93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595"' \
//     -o /tmp/attention_u3_row \
//     rust-verifier/scripts/cpp_vectors/attention_u3_row.cpp
// Run, with CPDUMP_FILE naming the output (rows are appended, one line per entry):
//   CPDUMP_FILE=/tmp/cpp_u3_rows.txt /tmp/attention_u3_row \
//     rust-verifier/fixtures/config rust-verifier/fixtures/ivk \
//     rust-verifier/fixtures/example.req rust-verifier/fixtures/example.y \
//     rust-verifier/fixtures/example.proof -id $(cat rust-verifier/fixtures/ID.txt) -q

// Every header cp_verify.cpp includes except vf_attention_check.h is included before the two
// macros below: their `g.main` members (blocks/frame/prints.h and others) must keep their names,
// while vf_attention_check.h must be parsed with the `doorH` macro in force.
#include "../../verifier/src/vf_subproof_segment.h"
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

#include <cstdio>
#include <cstdlib>
#include <cstring>

// The attention sub-proof's tree list is U3, PK_0 .. PK_3, ZZ, BZ, PXo (attention_check.h); the
// head sub-proof's last tree is PXf0 instead.
static bool attentionTrees(const HFork &F) {
  if (F.trees.size() != 8) return false;
  return F.trees[0].name == "U3" && F.trees[5].name == "ZZ" && F.trees[6].name == "BZ" &&
         F.trees[7].name == "PXo";
}

static void cpdumpRow(const char *tag, const std::vector<Ex> &L) {
  const char *path = std::getenv("CPDUMP_FILE");
  if (!path) path = "/tmp/cpp_u3_rows.txt";
  FILE *f = std::fopen(path, "a");
  if (!f) return;
  std::fprintf(f, "ROW %s len %zu\n", tag, L.size());
  for (size_t i = 0; i < L.size(); i++)
    std::fprintf(f, "%016llx %016llx %016llx\n", (unsigned long long)L[i].c[0],
                 (unsigned long long)L[i].c[1], (unsigned long long)L[i].c[2]);
  std::fclose(f);
}

static void cpdumpDoor(HFork &F, Tail2 &T, Tr &tr, u64 equationsLaid) {
  {
    const char *path = std::getenv("CPDUMP_FILE");
    if (!path) path = "/tmp/cpp_u3_rows.txt";
    FILE *f = std::fopen(path, "a");
    if (f) {
      std::fprintf(f, "DOOR trees %zu:", F.trees.size());
      for (const HTree &t : F.trees) std::fprintf(f, " %s", t.name.c_str());
      std::fprintf(f, "\n");
      std::fclose(f);
    }
  }
  if (attentionTrees(F)) {
    static int n = 0;
    char tag[64];
    std::snprintf(tag, sizeof tag, "attention-%d-U3-row0", n++);
    cpdumpRow(tag, F.trees[0].rows[0].L);
  }
  (doorH)(F, T, tr, equationsLaid);
}
// Function-like macro, expanded at the call sites in cp_verify.cpp's included headers. The
// parenthesized call inside cpdumpDoor() above is not expanded (the macro is defined after it).
#define doorH(F, T, tr, e) (cpdumpDoor((F), (T), (tr), (e)))

#define main cp_verify_original_main
#include "../../verifier/src/cp_verify.cpp"
#undef main

int main(int argc, char **argv) { return cp_verify_original_main(argc, argv); }
