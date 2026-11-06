// Copyright 2026 Anthropic PBC
// SPDX-License-Identifier: Apache-2.0
//
// Vectors for blocks/iop/message.h: the bytes of typed items, the list of items and marks, the
// append of a writer, and the reader's failure modes. Build with -DBLK_FIELD=2.

#include "hash/hash.h"
#include "iop/message.h"

#include <cstdio>
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
void read_all(const u8 *p, size_t n) {
  Reader r(p, n);
  const u8 *head = r.take(5);
  u64 w = 0;
  F x{};
  E y{};
  Digest d{};
  u64 z = 0;
  const bool ok = head != nullptr && r.get_u64(w) && r.get(x) && r.get(y) && r.get(d) && r.get_u64(z);
  std::printf("READ ok=%d at_end=%d head=", (int)ok, (int)r.at_end());
  if (head) {
    for (int i = 0; i < 5; i++) std::printf("%02x", head[i]);
  } else {
    std::printf("-");
  }
  std::printf(" w=%016llx f=%016llx e=", (unsigned long long)w, (unsigned long long)x.v);
  pv(y);
  pd(" d", d);
  std::printf(" z=%llu\n", (unsigned long long)z);
}
} // namespace

int main() {
  Digest d{};
  for (int i = 0; i < 8; i++) d.w[i] = 0x01020304u + (u32)i * 0x11111111u;

  Writer w;
  w.keep_list();
  w.mark("start");
  const u8 head[] = {0xde, 0xad, 0xbe, 0xef, 0x00};
  w.put_bytes(head, 5);
  w.put_u64(0x1122334455667788ull);
  w.put(F{0x123456789abcdef0ull});
  w.put(E{{F{1}, F{2}, F{3}}});
  w.put(d);
  {
    Writer inner;
    inner.keep_list();
    inner.put_u64(7);
    inner.mark("inner");
    w.append(inner);
  }
  w.mark("end");
  std::printf("HEX ");
  phex(w.bytes());
  std::printf("\n");
  std::printf("ITEMS n=%zu\n", w.items().size());
  for (const Writer::Item &i : w.items())
    std::printf("ITEM at=%zu bytes=%zu kind=%c\n", i.at, i.bytes, i.kind);
  std::printf("MARKS n=%zu\n", w.marks().size());
  for (const Writer::Mark &m : w.marks()) std::printf("MARK at=%zu words=%s\n", m.at, m.words.c_str());
  read_all(w.data(), w.size());

  // A writer without a list, appended to one: one item of plain bytes.
  Writer outer;
  outer.keep_list();
  outer.put_u64(9);
  {
    Writer plain;
    plain.put_u64(8);
    const u8 p[] = {1, 2};
    plain.put_bytes(p, 2);
    outer.append(plain);
  }
  std::printf("PLAIN ");
  phex(outer.bytes());
  std::printf("\nITEMS n=%zu\n", outer.items().size());
  for (const Writer::Item &i : outer.items())
    std::printf("ITEM at=%zu bytes=%zu kind=%c\n", i.at, i.bytes, i.kind);

  // Failures: a cut string, a symbol not below p, and leftovers.
  {
    Reader r(w.data(), 3);
    std::printf("CUT ok=%d\n", (int)(r.take(5) != nullptr));
  }
  {
    u8 b[8] = {0x01, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff}; // p = 2^64 - 2^32 + 1
    Reader r(b, 8);
    F x{};
    std::printf("NONCANON ok=%d\n", (int)r.get(x));
  }
  {
    u8 b[24] = {1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0xff, 0xff, 0xff, 0xff};
    Reader r(b, 24);
    E y{};
    std::printf("NONCANON_E ok=%d\n", (int)r.get(y));
  }
  {
    Reader r(w.data(), w.size() - 1);
    std::printf("LEFTOVER at_end=%d\n", (int)r.at_end());
  }
  return 0;
}
