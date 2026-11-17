#!/usr/bin/env python3
"""Recompute a FlashProve anchor digest from the artifact files and, optionally, compare it to an
anchored value. Standard library only; reads each file in chunks (the key and leaves are large).

  anchorDigest = SHA-256("FlashProve/anchor-v1\\0"
                         ‖ sha256(policy) ‖ sha256(layout) ‖ sha256(kl) ‖ sha256(key)
                         ‖ u32le(leafCount) ‖ sha256(leaf_0) ‖ … ‖ sha256(leaf_{n-1}))

usage: recompute-anchor.py <policy> <layout> <kl> <key> <leaf_0> [<leaf_1> ...] [--expect 0x<digest>]
Leaves are given in entry-number order. Exit 0 = recomputed (and matched, with --expect), 1 = mismatch.
"""
import hashlib
import struct
import sys

DOMAIN = b"FlashProve/anchor-v1\x00"


def file_sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.digest()


def anchor_digest(policy, layout, kl, key, leaves):
    h = hashlib.sha256(DOMAIN)
    for p in (policy, layout, kl, key):
        h.update(file_sha256(p))
    h.update(struct.pack("<I", len(leaves)))
    for p in leaves:
        h.update(file_sha256(p))
    return h.digest()


REF_DOMAIN = b"FlashProve/anchor-ref-v1\x00"


def _addr(a):
    b = bytes.fromhex(a.lower().removeprefix("0x"))
    if len(b) != 20:
        raise SystemExit(f"not a 20-byte address: {a}")
    return b


def anchor_ref(chain_id, registry, anchorer, commitment_id):
    """anchorRef = SHA-256(REF_DOMAIN || u256be(chainId) || registry || anchorer || commitmentId) -- the
    key of one anchor row; the content digest above stays chain-free."""
    cid = bytes.fromhex(commitment_id.lower().removeprefix("0x"))
    if len(cid) != 32:
        raise SystemExit("commitment ID must be 32 bytes")
    return hashlib.sha256(REF_DOMAIN + int(chain_id).to_bytes(32, "big") + _addr(registry) + _addr(anchorer) + cid).digest()


def main(argv):
    if argv[:1] == ["--ref"]:   # --ref CHAIN_ID REGISTRY ANCHORER COMMITMENT_ID [--expect REF]
        a = argv[1:]
        exp = None
        if "--expect" in a:
            i = a.index("--expect"); exp = a[i + 1].lower().removeprefix("0x"); a = a[:i] + a[i + 2:]
        if len(a) != 4:
            print(__doc__, file=sys.stderr)
            return 64
        got = anchor_ref(*a).hex()
        print(f"anchor ref: 0x{got}")
        if exp is None:
            return 0
        print("RECOMPUTED: matches the anchor ref" if got == exp else f"MISMATCH: expected 0x{exp}")
        return 0 if got == exp else 1
    expect = None
    if "--expect" in argv:
        i = argv.index("--expect")
        expect = argv[i + 1].lower().removeprefix("0x")
        argv = argv[:i] + argv[i + 2:]
    if len(argv) < 5:
        print(__doc__, file=sys.stderr)
        return 64
    got = anchor_digest(*argv[:4], argv[4:]).hex()
    print(f"anchor digest: 0x{got}")
    if expect is None:
        return 0
    if got == expect:
        print("RECOMPUTED: matches the anchored digest")
        return 0
    print(f"MISMATCH: anchored 0x{expect}")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
