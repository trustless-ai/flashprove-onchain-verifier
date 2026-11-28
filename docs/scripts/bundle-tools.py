#!/usr/bin/env python3
"""Small ABI helper for the local on-chain verification script.

Commands:
  tamper <bundle> <out_bundle> <proof|pv> <out_json>
  check-tx <tx_json> <expected_bundle> <out_json>
"""
import hashlib
import json
import sys

def word(n):
    return int(n).to_bytes(32, "big")

def pad(b):
    return b + b"\0" * ((32 - len(b) % 32) % 32)

def decode_bundle(data):
    if len(data) < 96:
        raise ValueError("bundle shorter than two offset words")
    o_pv = int.from_bytes(data[0:32], "big")
    o_proof = int.from_bytes(data[32:64], "big")
    if o_pv + 32 > len(data) or o_proof + 32 > len(data):
        raise ValueError("bundle offset out of range")
    n_pv = int.from_bytes(data[o_pv:o_pv + 32], "big")
    pv = data[o_pv + 32:o_pv + 32 + n_pv]
    n_proof = int.from_bytes(data[o_proof:o_proof + 32], "big")
    proof = data[o_proof + 32:o_proof + 32 + n_proof]
    if len(pv) != n_pv or len(proof) != n_proof:
        raise ValueError("bundle truncated")
    return pv, proof

def encode_bundle(pv, proof):
    o_pv = 64
    o_proof = o_pv + 32 + len(pad(pv))
    return word(o_pv) + word(o_proof) + word(len(pv)) + pad(pv) + word(len(proof)) + pad(proof)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def load_tx(path):
    obj = json.load(open(path))
    if isinstance(obj.get("data"), dict):
        obj = obj["data"]
    if "input" not in obj:
        raise ValueError("tx JSON has no input")
    return obj

def decode_verify_input(raw_hex):
    raw = bytes.fromhex(raw_hex[2:] if raw_hex.startswith("0x") else raw_hex)
    if len(raw) < 4:
        raise ValueError("input shorter than selector")
    selector = raw[:4].hex()
    if selector != "f2fd7e98":
        raise ValueError("unexpected verify selector: " + selector)
    body = raw[4:]
    if len(body) < 5 * 32:
        raise ValueError("verify input shorter than head")
    words = [body[i * 32:(i + 1) * 32] for i in range(5)]
    off = int.from_bytes(words[4], "big")
    n = int.from_bytes(body[off:off + 32], "big")
    bundle = body[off + 32:off + 32 + n]
    if len(bundle) != n:
        raise ValueError("verify input bundle truncated")
    return selector, words[0], words[1], words[2], words[3], bundle

def explain(bundle):
    pv, proof = decode_bundle(bundle)
    return {
        "bundle_len": len(bundle),
        "bundle_sha256": sha(bundle),
        "pv_len": len(pv),
        "pv_sha256": sha(pv),
        "proof_len": len(proof),
        "proof_sha256": sha(proof),
    }

def cmd_tamper(src, dst, field, out):
    data = open(src, "rb").read()
    pv, proof = decode_bundle(data)
    if len(data) != 7232 or len(pv) != 6711 or len(proof) != 356:
        raise SystemExit("unexpected bundle/field size; refusing fixed-offset tamper")
    if encode_bundle(pv, proof) != data:
        raise SystemExit("original bundle does not round-trip through the ABI codec")
    if field == "proof":
        target, other, offset = proof, pv, 355
    elif field == "pv":
        target, other, offset = pv, proof, 6710
    else:
        raise SystemExit("field must be proof or pv")
    if offset != len(target) - 1:
        raise SystemExit("unexpected field length")
    new_target = bytearray(target)
    new_target[offset] ^= 1
    changed = [i for i, (a, b) in enumerate(zip(target, new_target)) if a != b]
    if changed != [offset]:
        raise SystemExit("target field did not change exactly one byte")
    if other != (pv if field == "proof" else proof):
        raise SystemExit("other field changed")
    new_pv, new_proof = (bytes(new_target), other) if field == "pv" else (other, bytes(new_target))
    new_data = encode_bundle(new_pv, new_proof)
    diff = [i for i, (a, b) in enumerate(zip(data, new_data)) if a != b]
    if len(diff) != 1:
        raise SystemExit("re-encoded bundle changed more than one byte")
    if len(new_data) != len(data):
        raise SystemExit("re-encoded bundle length changed")
    open(dst, "wb").write(new_data)
    result = {
        "field": field,
        "field_offset": offset,
        "field_size": len(target),
        "field_sha256_before": sha(target),
        "field_sha256_after": sha(new_target),
        "other_field_size": len(other),
        "other_field_sha256_before": sha(other),
        "other_field_sha256_after": sha(other),
        "target_changed_offsets": changed,
        "other_field_unchanged": True,
        "bundle_len_before": len(data),
        "bundle_len_after": len(new_data),
        "bundle_sha256_before": sha(data),
        "bundle_sha256_after": sha(new_data),
        "bundle_changed_offsets": diff,
        "bundle_single_byte_change": True,
    }
    json.dump(result, open(out, "w"), indent=2, sort_keys=True)
    print(json.dumps(result, sort_keys=True))

def cmd_check_tx(tx_path, expected_bundle, out):
    tx = load_tx(tx_path)
    selector, task, agent, input_hash, output_hash, actual = decode_verify_input(tx["input"])
    expected = open(expected_bundle, "rb").read()
    exact = actual == expected
    result = {
        "selector": "0x" + selector,
        "task": "0x" + task.hex(),
        "agent": "0x" + agent.hex(),
        "input_hash": "0x" + input_hash.hex(),
        "output_hash": "0x" + output_hash.hex(),
        "expected_bundle_len": len(expected),
        "expected_bundle_sha256": sha(expected),
        "actual_bundle_len": len(actual),
        "actual_bundle_sha256": sha(actual),
        "bundle_exact_match": exact,
    }
    result.update({("actual_" + k): v for k, v in explain(actual).items()})
    result.update({("expected_" + k): v for k, v in explain(expected).items()})
    json.dump(result, open(out, "w"), indent=2, sort_keys=True)
    print(json.dumps({"bundle_exact_match": exact, "actual_bundle_sha256": result["actual_bundle_sha256"]}))
    if not exact:
        raise SystemExit("actual transaction calldata bundle does not match the tested bundle")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    if sys.argv[1] == "tamper" and len(sys.argv) == 6:
        cmd_tamper(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])
    elif sys.argv[1] == "check-tx" and len(sys.argv) == 5:
        cmd_check_tx(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        raise SystemExit(__doc__)
