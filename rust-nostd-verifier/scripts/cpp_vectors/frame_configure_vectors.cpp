// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0

// Vectors for `configure` (blocks/frame/configure.h):
//   ProofVerdict, RequestFixed, Shapes/ShapesOf, Configured and its accessors, configure(),
//   published_id() and the hiding conditions it tests (blocks/frame/hiding_conditions.h).
//
// Usage: frame_configure_vectors <parameters-that-the-stand-in-fits.txt>
//
// One parameter file, the stand-in sub-proofs, a layout of 25 empty links, 25 identifiers and one
// range check that passes; then deterministic mutations of the shapes that reach each of
// configure's later cross-checks: no range checks, a layout with a link fewer, an identifier
// fewer, no pending row, a plain scalar on a link that is not the last, and an extra message at
// the start. The last group mutates a `KeyFixed` that the accepted configuration gives, one field
// at a time, to show every later reason of `key_fault`. `key_fault`'s first two reasons (the LIN
// and WF shapes) are already tested at the end of `lin_sized`/`wf_sized`, so no `Shapes` that
// `sized` accepts can reach them through `configure`.
//
// `fp-host/tests/frame_configure_vectors.rs` rebuilds every case with the port and renders the
// same lines; the only fields compared with a tolerance are the doubles that go through libm
// (the accounting's figures), and those are printed as their bit patterns.
//
// The `OneList` counter: the C++ headers keep it in a static; the port passes a fresh counter per
// file. The numbers are never printed.

#include <cstdio>
#include <cstring>
#include <fstream>
#include <string>
#include <utility>
#include <vector>

#include "frame/configure.h"
#include "frame/heads.h"
#include "hash/hash.h"
#include "iop/message.h"
#include "iop/req.h"
#include "numbers/accounting.h"

using namespace blk;

namespace {

std::string hex(const std::string &s) {
  static const char *d = "0123456789abcdef";
  std::string o;
  o.reserve(2 * s.size());
  for (unsigned char c : s) o += d[c >> 4], o += d[c & 15];
  return o;
}

std::string hex_or_dash(const std::string &s) { return s.empty() ? "-" : hex(s); }

std::string bytes_hex(const std::vector<u8> &v) {
  static const char *d = "0123456789abcdef";
  std::string o;
  o.reserve(2 * v.size());
  for (u8 c : v) o += d[c >> 4], o += d[c & 15];
  return o;
}

std::string digest_hex(const Digest &x) {
  u8 b[DIGEST_BYTES];
  digest_to_bytes(x, b);
  return bytes_hex(std::vector<u8>(b, b + DIGEST_BYTES));
}

unsigned long long dbits(double d) {
  unsigned long long u;
  std::memcpy(&u, &d, sizeof u);
  return u;
}

std::string shape_str(const OracleShape &o) {
  char b[512];
  std::snprintf(b, sizeof b,
                "name=%s code=%u main_rows=%llu main_deg=%u mask_rows=%llu mask_code=%u "
                "answers=%u",
                hex(o.name).c_str(), o.code, (unsigned long long)o.main_rows, o.main_deg,
                (unsigned long long)o.mask_rows, o.mask_code, o.answers);
  return b;
}

std::string table_str(const TableSize &t) {
  char b[512];
  std::snprintf(b, sizeof b,
                "log_n=%u ell=%llu r=%llu v=%u answers=%u radius=%llu later=%llu m_once=%llu "
                "m_later=%llu",
                t.code.log_n, (unsigned long long)t.code.ell, (unsigned long long)t.code.r, t.v,
                t.answers, (unsigned long long)t.distances.radius,
                (unsigned long long)t.distances.later_radius,
                (unsigned long long)t.distances.m_once,
                (unsigned long long)t.distances.m_later);
  return b;
}

std::string index_str(const IndexShape &s) {
  char b[512];
  std::snprintf(b, sizeof b,
                "log_n=%u ell=%llu r=%llu v=%u answers=%u salt=%llu radius=%llu later=%llu "
                "m_once=%llu m_later=%llu",
                s.code.log_n, (unsigned long long)s.code.ell, (unsigned long long)s.code.r, s.v,
                s.answers, (unsigned long long)s.salt_bytes,
                (unsigned long long)s.distances.radius,
                (unsigned long long)s.distances.later_radius,
                (unsigned long long)s.distances.m_once, (unsigned long long)s.distances.m_later);
  return b;
}

void dump_codes(const std::string &name, const Codes &codes) {
  for (size_t i = 0; i < codes.base.size(); i++)
    std::printf("CODES name=%s i=%zu kind=base log_n=%u ell=%llu r=%llu\n", name.c_str(), i,
                codes.base[i].log_n, (unsigned long long)codes.base[i].ell,
                (unsigned long long)codes.base[i].r);
  for (size_t i = 0; i < codes.mask.size(); i++)
    std::printf("CODES name=%s i=%zu kind=mask log_n=%u ell=%llu r=%llu\n", name.c_str(), i,
                codes.mask[i].log_n, (unsigned long long)codes.mask[i].ell,
                (unsigned long long)codes.mask[i].r);
}

std::string ids_str(const std::vector<u64> &ids) {
  if (ids.empty()) return "-";
  std::string o;
  for (size_t i = 0; i < ids.size(); i++) {
    if (i) o += ",";
    o += std::to_string((unsigned long long)ids[i]);
  }
  return o;
}

std::string parts_str(const std::vector<std::string> &parts) {
  if (parts.empty()) return "-";
  std::string o;
  for (size_t i = 0; i < parts.size(); i++) {
    if (i) o += ",";
    o += hex(parts[i]);
  }
  return o;
}

RangeCheck good_check() {
  RangeCheck c;
  c.rows = 1, c.columns = 1, c.combinations = 1, c.bound = 2, c.range = 1u << 19;
  c.digit_bits[0] = 10, c.digit_bits[1] = 10;
  return c;
}

// ---- the caller's Shapes, one variant at a time ----
enum Variant { BASE = 0, NO_CHECKS, LAYOUT_SHORT, IDENTIFIERS_SHORT, PENDING_ZERO, PLAIN_FIRST, EXTRA_AT_START };
int g_variant = BASE;

Shapes shapes_for(int variant) {
  Shapes s;
  s.sub = stand_in_subproofs();
  s.layout.link.assign(s.sub.request.link.size(), {});
  for (size_t i = 0; i < s.sub.request.link.size(); i++) s.identifiers.push_back(1000 + i);
  s.range_checks.push_back(good_check());
  switch (variant) {
    case NO_CHECKS: s.range_checks.clear(); break;
    case LAYOUT_SHORT: s.layout.link.resize(s.sub.request.link.size() - 1); break;
    case IDENTIFIERS_SHORT: s.identifiers.pop_back(); break;
    case PENDING_ZERO: s.sub.pending_rows = 0; break;
    case PLAIN_FIRST: s.sub.request.link[0].plain = 1; break;
    case EXTRA_AT_START: {
      OracleShape o;
      o.name = "extra at the start", o.code = 0, o.main_rows = 0, o.main_deg = 1, o.mask_rows = 1;
      o.mask_code = 0, o.answers = 1;
      s.sub.request.at_start.push_back(OracleNotice{o, 100});
      break;
    }
    default: break;
  }
  return s;
}

Shapes shapes_of(const std::vector<std::string> &files, const Parameters &par) {
  return shapes_for(g_variant);
}

std::string req_bytes(const ReqShape &s) {
  Writer w;
  public_bytes(w, s);
  return bytes_hex(w.bytes());
}

std::string layout_bytes(const ReqLayout &l) {
  Writer w;
  public_bytes(w, l);
  return bytes_hex(w.bytes());
}

size_t layout_arrays(const ReqLayout &l) {
  size_t n = 0;
  for (const std::vector<ReqArray> &link : l.link) n += link.size();
  return n;
}

void dump_test(const std::string &name, const char *test, const TestSizes &x) {
  std::printf("LTEST name=%s test=%s t=%llu stages=%zu group_name=%s group_k=%u group_h=%u\n",
              name.c_str(), test, (unsigned long long)x.t, x.stages.size(),
              hex(x.group.name).c_str(), x.group.k, x.group.h);
}

void dump_sized(const std::string &name, const Configured &c) {
  const Sized &z = c.sized();
  std::printf("SIZED name=%s refused=%s request_bytes=%s\n", name.c_str(),
              hex_or_dash(z.refused).c_str(), req_bytes(z.request).c_str());
  dump_codes(name + "/proof", z.proof_codes);
  dump_codes(name + "/key", z.key_codes);
  dump_codes(name + "/entry", z.entry_codes);
  for (int once = 0; once < 2; once++) {
    const LinSized &x = once ? z.once : z.batch;
    const LinShape &S = x.S;
    std::printf(
        "LSIZED name=%s refused=%s k_lo=%u matrix_rows=%llu columns=%llu batches=%llu "
        "shared_split=%d own_split=%d tests=%zu,%zu,%zu,%zu input=%s input_leaf=%u table=%s\n",
        once ? "once" : "batch", hex_or_dash(x.refused).c_str(), S.k_lo,
        (unsigned long long)S.matrix_rows, (unsigned long long)S.fold.columns,
        (unsigned long long)x.batches, S.shared_split_needed() ? 1 : 0,
        S.own_split_needed() ? 1 : 0, S.test_u.size(), S.test_omega.size(), S.test_own.size(),
        S.test_own_omega.size(), shape_str(x.input.shape).c_str(), x.input.leaf_class,
        table_str(x.table).c_str());
    dump_test(once ? "once" : "batch", "folded", x.folded);
  }
  const WfSized &w = z.ranges;
  std::printf(
      "WSIZED refused=%s k_col=%u rows=%llu message_id=%u pending=%zu lookups=%zu stages=%zu "
      "message=%s message_leaf=%u ride=%d\n",
      hex_or_dash(w.refused).c_str(), w.matrix.k_col, (unsigned long long)w.matrix.rows,
      w.x.message_id, w.pending, w.x.lookups.size(), w.x.stages.size(),
      shape_str(w.x.message.shape).c_str(), w.x.message.leaf_class,
      w.x.choice.masks_ride ? 1 : 0);
  dump_test("ranges", "test", w.test);
  const LinkSized &k = z.link;
  std::printf(
      "LINKSIZED refused=%s columns_first=%llu columns_further=%llu code=%u mask_code=%u "
      "rows=%llu rows_high=%d leaf_class=%u masks_ahead=%d ride=%d later=%zu table=%s\n",
      hex_or_dash(k.refused).c_str(), (unsigned long long)k.S.columns_first,
      (unsigned long long)k.S.columns_further, k.S.code, k.S.mask_code,
      (unsigned long long)k.S.rows, k.S.rows_high ? 1 : 0, k.S.leaf_class,
      k.S.masks_ahead ? 1 : 0, k.S.choice.masks_ride ? 1 : 0, k.S.later.size(),
      index_str(k.S.table).c_str());
  dump_test("link", "linked", k.linked);
  std::printf("TABLE %s\n", table_str(z.d.table).c_str());
}

void dump_file(const char *label, const FilePlan &f) {
  std::printf("FILE name=%s head_words=%u place_depth=%u has_place=%d chains=%zu\n", label,
              f.head_words, f.place_depth, f.has_place ? 1 : 0, f.chains.size());
  for (size_t i = 0; i < f.chains.size(); i++) {
    const Planned &q = f.chains[i].plan;
    std::printf("CHAIN file=%s i=%zu name=%s parts=%zu parts_names=%s rounds=%zu messages=%zu "
                "holds=%d names=%d queries=%llu\n",
                label, i, hex(f.chains[i].name).c_str(), q->parts.size(),
                parts_str(q->parts).c_str(), q->rounds_.size(), q->messages_.size(),
                q->holds() ? 1 : 0, q->names_of_the_format() ? 1 : 0,
                (unsigned long long)q->queries());
  }
}

void dump_account(const char *label, const Configured &c, const FilePlan &f) {
  const Accounting a = account(merged(c.sized().d.set, {f}));
  std::printf(
      "ACCOUNT file=%s refused=%s needs_work=%d holds=%d rounds=%llu queries=%llu lists_bits=%llu "
      "lists_work=%u sum=%llu sum_lists=%llu planned_calls=%llu\n",
      label, hex_or_dash(a.refused).c_str(), a.needs_work ? 1 : 0, a.holds ? 1 : 0,
      (unsigned long long)a.rounds, (unsigned long long)a.queries, dbits(a.lists.bits),
      a.lists.work, dbits(a.sum), dbits(a.sum_lists), (unsigned long long)a.planned_calls);
}

void dump_work(const char *label, const Configured::Work &w) {
  std::printf("WORK name=%s needed=%d bits_without=%llu bits=%u\n", label, w.needed ? 1 : 0,
              dbits(w.bits_without), w.bits);
}

void dump_fixed(const Configured &c) {
  const RequestFixed &f = c.fixed();
  const Configured::TableColumns t = c.table_columns();
  std::printf(
      "TABLECOLUMNS bears=%llu one_time=%llu link_on_the_first=%llu link_on_the_further=%llu "
      "a_batch=%llu batches=%llu\n",
      (unsigned long long)t.bears, (unsigned long long)t.one_time,
      (unsigned long long)t.link_on_the_first, (unsigned long long)t.link_on_the_further,
      (unsigned long long)t.a_batch, (unsigned long long)t.batches);
  std::printf(
      "FIXED configuration=%s pending_rows=%llu ids_n=%zu ids=%s binding_log_leaves=%u "
      "binding_salt_bytes=%llu\n",
      digest_hex(f.configuration).c_str(), (unsigned long long)f.pending_rows,
      f.identifiers.size(), ids_str(f.identifiers).c_str(), f.binding.log_leaves,
      (unsigned long long)f.binding.salt_bytes);
  dump_codes("fixed", f.codes);
  const LinShape &S = f.lin;
  std::printf(
      "FIXLIN k_lo=%u matrix_rows=%llu columns=%llu masks_ahead=%d ride=%d shared_split=%d "
      "own_split=%d omega_lc=%u split_lc=%u w_lc=%u own_lc=%u tests=%zu,%zu,%zu,%zu\n",
      S.k_lo, (unsigned long long)S.matrix_rows, (unsigned long long)S.fold.columns,
      S.masks_ahead ? 1 : 0, S.choice.masks_ride ? 1 : 0, S.shared_split_needed() ? 1 : 0,
      S.own_split_needed() ? 1 : 0, S.omega_leaf_class, S.shared_split_leaf_class, S.w_leaf_class,
      S.own_split_leaf_class, S.test_u.size(), S.test_omega.size(), S.test_own.size(),
      S.test_own_omega.size());
  std::printf("FIXREQ bytes=%s\n", req_bytes(f.shape).c_str());
  std::printf("LAYOUT links=%zu arrays=%zu bytes=%s\n", f.layout.link.size(),
              layout_arrays(f.layout), layout_bytes(f.layout).c_str());
  std::printf("RANGECHECKS n=%zu\n", c.range_checks().size());
  for (size_t i = 0; i < c.range_checks().size(); i++) {
    const RangeCheck &r = c.range_checks()[i];
    std::printf(
        "RANGECHECK i=%zu rows=%llu columns=%llu combinations=%llu bound=%llu range=%llu "
        "digit_bits=%u,%u bits=%ld\n",
        i, (unsigned long long)r.rows, (unsigned long long)r.columns,
        (unsigned long long)r.combinations, (unsigned long long)r.bound,
        (unsigned long long)r.range, r.digit_bits[0], r.digit_bits[1],
        (long)range_check_bits(r));
  }
  const char *fault = key_fault(key_fixed(c.sized(), c.fixed().configuration));
  std::printf("KEYFAULT %s\n", fault ? hex(fault).c_str() : "-");
}

void dump_case(const char *name, const Configured &c) {
  std::printf("CASE name=%s\n", name);
  std::printf("REFUSED %s\n", hex_or_dash(c.refused()).c_str());
  dump_sized(name, c);
  dump_file("proof", c.proof());
  dump_file("key", c.key());
  dump_file("entry", c.entry());
  dump_account("proof", c, c.proof());
  dump_account("key", c, c.key());
  dump_account("entry", c, c.entry());
  dump_work("proof", Configured::Work{c.needs_work(), c.bits_without_work(), c.work()});
  dump_work("key", c.work_of_the_key());
  dump_work("entry", c.work_of_an_entry());
  dump_fixed(c);
}

void dump_key_fault_case(const char *name, const char *what, const KeyFixed &f) {
  const char *why = key_fault(f);
  std::printf("KEYFAULT2 name=%s case=%s fault=%s\n", name, what, why ? hex(why).c_str() : "-");
}

// The later checks of key_fault(): one field broken at a time on a key that otherwise passes.
void dump_key_fault_cases(const char *name, const KeyFixed &base) {
  dump_key_fault_case(name, "base", base);
  {
    KeyFixed f = base;
    f.lin.matrix_rows = 0;
    dump_key_fault_case(name, "lin", f);
  }
  {
    KeyFixed f = base;
    f.ranges.lookups.clear();
    dump_key_fault_case(name, "ranges", f);
  }
  {
    KeyFixed f = base;
    f.binding.log_leaves = 1;
    dump_key_fault_case(name, "binding", f);
  }
  {
    KeyFixed f = base;
    f.ranges.message_id = 0;
    dump_key_fault_case(name, "message_id", f);
  }
  {
    KeyFixed f = base;
    f.index_masks.shape.main_rows = 1;
    dump_key_fault_case(name, "mask_main_rows", f);
  }
  {
    KeyFixed f = base;
    f.index_masks.shape.mask_rows = 0;
    dump_key_fault_case(name, "mask_no_rows", f);
  }
  {
    KeyFixed f = base;
    f.index_masks.shape.answers = 0;
    dump_key_fault_case(name, "mask_no_answers", f);
  }
  {
    KeyFixed f = base;
    f.index_masks.shape.mask_code = (unsigned)f.codes.mask.size();
    dump_key_fault_case(name, "mask_code", f);
  }
  {
    KeyFixed f = base;
    f.index_masks.shape.mask_rows = 1;
    const unsigned code = f.index_masks.shape.mask_code;
    f.index_masks.shape.answers =
        f.codes.mask.empty() ? 1u
                             : (unsigned)f.codes.mask[code < f.codes.mask.size() ? code : 0].ell;
    dump_key_fault_case(name, "mask_no_room", f);
  }
}

bool read_file(const char *path, std::string &text) {
  std::ifstream f(path, std::ios::binary);
  if (!f) return false;
  text.assign((std::istreambuf_iterator<char>(f)), std::istreambuf_iterator<char>());
  return true;
}

}  // namespace

int main(int argc, char **argv) {
  if (argc != 2) {
    std::fprintf(stderr, "usage: frame_configure_vectors <parameters.txt>\n");
    return 2;
  }
  std::string text;
  if (!read_file(argv[1], text)) {
    std::fprintf(stderr, "frame_configure_vectors: cannot read %s\n", argv[1]);
    return 2;
  }
  const std::vector<std::string> files{text};
  static const char *names[] = {"base",         "no_checks",     "layout_short", "identifiers_short",
                                "pending_zero", "plain_first",   "extra_at_start"};
  for (int v = BASE; v <= EXTRA_AT_START; v++) {
    g_variant = v;
    const Configured c = configure(files, shapes_of);
    dump_case(names[v], c);
  }
  g_variant = BASE;
  const Configured c = configure(files, shapes_of);
  const KeyFixed key = key_fixed(c.sized(), c.fixed().configuration);
  dump_key_fault_cases("base", key);
  return 0;
}
