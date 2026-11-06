// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for `wf_shape_of_units` and `wf_units_fault` (`blocks/frame/wf_units.h`). Each case dumps
// the two lookups (name, d, digit weights, offset, first bound, entries) or the first fault.
//
// Usage: frame_wf_units_vectors

#include <cstdio>
#include <string>
#include <vector>

#include "frame/wf_units.h"

using namespace blk;

static std::string f_str(F x) {
  char b[64];
  std::snprintf(b, sizeof b, "%016llx", (unsigned long long)x.v);
  return b;
}

static void dump_lookup(const WfShapeLookup &l) {
  std::printf("LOOKUP name=%s d=%u mu=%u live=%u weights=", l.lookup.name.c_str(), l.lookup.d,
              l.lookup.mu, l.lookup.live);
  for (size_t i = 0; i < l.lookup.digit_weight.size(); i++)
    std::printf("%s%s", i ? "," : "", f_str(l.lookup.digit_weight[i]).c_str());
  std::printf(" offset=%s padding=%s first_bound=", f_str(l.lookup.offset).c_str(),
              f_str(l.lookup.padding_key).c_str());
  if (l.lookup.first_bound.empty()) std::printf("-");
  for (size_t i = 0; i < l.lookup.first_bound.size(); i++)
    std::printf("%s%u", i ? "," : "", l.lookup.first_bound[i]);
  std::printf(" entries=");
  for (size_t i = 0; i < l.entries.size(); i++)
    std::printf("%s%llu:%llu:%llu:%llu", i ? ";" : "", (unsigned long long)l.entries[i].first_place,
                (unsigned long long)l.entries[i].first_row, (unsigned long long)l.entries[i].places,
                (unsigned long long)l.entries[i].stride);
  std::printf(" log_rows_apart=%u\n", l.log_rows_apart);
}

static void shape(const char *name, unsigned k_col, u64 matrix_rows, u64 ranged_rows,
                  const std::vector<WfUnit> &units) {
  const char *fault = wf_units_fault(matrix_rows, ranged_rows, units);
  std::printf("WFUNITS name=%s fault=%s k_col=%u matrix_rows=%llu ranged_rows=%llu\n", name,
              fault ? fault : "-", k_col, (unsigned long long)matrix_rows,
              (unsigned long long)ranged_rows);
  if (fault) return;
  const WfShape s = wf_shape_of_units(k_col, matrix_rows, ranged_rows, units);
  std::printf("WFLOOKUPS name=%s count=%zu\n", name, s.lookups.size());
  for (const WfShapeLookup &l : s.lookups) dump_lookup(l);
}

int main() {
  const std::vector<WfUnit> mixed = {{0, 80, 2}, {80, 16, 4}, {96, 4, 2}};
  shape("mixed", 11, 100, 100, mixed);
  shape("mixed_k8", 8, 100, 100, mixed);
  shape("mixed_k9", 9, 100, 100, mixed);
  shape("tail_bytes", 11, 108, 108, {{0, 80, 2}, {80, 16, 4}, {96, 10, 2}});
  shape("four_digits_only", 11, 40, 40, {{0, 40, 4}});
  shape("empty", 11, 100, 100, {});
  shape("odd_ranged", 11, 100, 99, mixed);
  shape("ranged_more", 11, 90, 100, mixed);
  shape("matrix_big", 11, 1ull << 40, 1ull << 40, {{0, 1ull << 40, 2}});
  shape("digit_three", 11, 100, 100, {{0, 80, 3}});
  shape("rows_zero", 11, 100, 100, {{0, 0, 2}});
  shape("rows_odd", 11, 100, 100, {{0, 81, 2}});
  shape("gap", 11, 100, 100, {{0, 80, 2}, {82, 18, 2}});
  shape("overlap", 11, 100, 100, {{0, 82, 2}, {80, 20, 2}});
  shape("beyond", 11, 100, 100, {{0, 80, 2}, {80, 22, 2}});
  return 0;
}
