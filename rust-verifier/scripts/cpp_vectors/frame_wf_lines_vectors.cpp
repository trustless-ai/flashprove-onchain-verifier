// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for `wf_cut`/`wf_parts_of`/`wf_planes_of`/`wf_lines` (`blocks/frame/wf_frame.h`).
//
// Usage: frame_wf_lines_vectors

#include <cstdio>
#include <string>
#include <vector>

#include "frame/wf_frame.h"
#include "frame/wf_units.h"

using namespace blk;

static std::string runs_str(const std::vector<WfRun> &runs) {
  std::string s;
  for (size_t i = 0; i < runs.size(); i++) {
    if (i) s += ";";
    s += std::to_string(runs[i].first_place) + ":" + std::to_string(runs[i].first_row) + ":" +
         std::to_string(runs[i].places) + ":" + std::to_string(runs[i].stride);
  }
  return s;
}

static void cut(const char *name, const std::vector<WfRun> &entries, unsigned log_places,
                unsigned log_rows_apart) {
  const u64 n = wf_parts_of(entries, log_places, log_rows_apart);
  const std::vector<WfPart> parts = wf_cut(entries, log_places, log_rows_apart);
  std::printf("CUT name=%s parts_of=%llu parts=%zu planes=%u\n", name, (unsigned long long)n,
              parts.size(), wf_planes_of(parts, 11));
  for (size_t i = 0; i < parts.size(); i++)
    std::printf("PART name=%s i=%zu log_places=%u runs=%s\n", name, i, parts[i].log_places,
                runs_str(parts[i].runs).c_str());
}

int main() {
  const std::vector<WfRun> two = {{0, 0, 40, 40}, {0, 96, 2, 2}};
  const std::vector<WfRun> apart = {{0, 0, 40, 40}, {0, 96, 2, 2}};
  cut("two", two, 6, 0);
  cut("two_apart", apart, 6, 1);
  cut("small_part", two, 2, 0);
  cut("exact_part", two, 5, 0);
  {
    const WfShapeLookup l{{"look", 8, 0, 0, {F::one()}, from_u64(128), F::zero(), {}, {}},
                          {{0, 0, 40, 40}, {0, 96, 2, 2}},
                          1};
    const WfShape shape{11, 100, {l}};
    for (unsigned part_log : {11u, 9u, 6u, 5u, 4u, 20u, 63u}) {
      const WfLines L = wf_lines(shape, GroupLine(), part_log);
      std::printf("LINES part_log=%u fault=%s lookups=%zu\n", part_log, L.fault ? L.fault : "-",
                  L.lookups.size());
      for (size_t i = 0; i < L.lookups.size(); i++) {
        const WfLookup &x = L.lookups[i];
        std::printf("LINE lookup=%zu name=%s mu=%u live=%u parts=%zu\n", i, x.name.c_str(), x.mu,
                    x.live, x.parts.size());
        for (size_t j = 0; j < x.parts.size(); j++)
          std::printf("LPART lookup=%zu i=%zu log_places=%u runs=%s\n", i, j, x.parts[j].log_places,
                      runs_str(x.parts[j].runs).c_str());
      }
    }
  }
  return 0;
}
