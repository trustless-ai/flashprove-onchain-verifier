# The on-chain verifiers

This directory holds two stateless `IProofVerifier` implementations — ERC-8274's inner,
algorithm-specific layer. An `IAgentVerifier` wraps either of them, keeps the state, and decides
which verdicts count as an answer. Which one an application picks is a question of what evidence
it trusts, not of what the interface looks like.

| Directory | Contract | `proofSystem()` | Accepts |
|---|---|---|---|
| `src/zk` | `FlashProveZKVerifier` | `"zk/sp1"` | an SP1 proof over FPV1 public values |
| `src/attestation` | `FlashProveAttestVerifier` | `"attestation/multisig"` | signatures from a pre-approved committee |

One instance serves every application. Neither path stores an agent, a task, a commitment ID or a
verdict policy; deployment-time configuration arrives with each call inside `metadata`.

```
IAgentVerifiable  ──►  IAgentVerifier  ──┬─►  FlashProveZKVerifier  ──►  ISP1Verifier
 (settlement)          (application,     │    (stateless)              (the chain's
                        stateful,        │                             SP1 verifier)
                        per app)         │
                                         └─►  FlashProveAttestVerifier  ──►  (nothing else:
                                              (stateless)                    it checks signatures)
```

## The call they share

```solidity
function verify(
    bytes32 inputHash,       // commitment to the model input
    bytes32 outputHash,      // commitment to the model output
    bytes calldata metadata, // deployment-time configuration, held by the IAgentVerifier
    bytes calldata proof     // per-inference evidence
) external view returns (bool);
```

What `metadata` and `proof` carry is each backend's business, and both are documented below. In
the zk path, `true` requires all three:

1. the SP1 verifier on this chain accepts `sp1Proof` for `programVKey` over `publicValues`;
2. the FPV1 block's `input_digest` equals `inputHash`;
3. the FPV1 block's `result_v1_digest` equals `outputHash`.

In the attestation path, `true` requires `threshold` distinct committee signatures over the
same attestation — see [The attestation path](#the-attestation-path) for the signed preimage and
the bundle encoding.

Neither path reverts on a bad proof: both return `false`, so the outer layer can record the
attempt either way, and a revert there would throw the record away.

## What it says about itself

Both implementations answer the same three calls; only the reported backend differs.

| Call | `FlashProveZKVerifier` | `FlashProveAttestVerifier` |
|---|---|---|
| `proofSystem()` | `"zk/sp1"` | `"attestation/multisig"` |
| `proofProfile()` | `keccak256(abi.encode(PROOF_SYSTEM, address(this).codehash))` | same construction |
| `supportsInterface` | `IProofVerifier` and `IERC165` | same |

The contract name carries the product; the backend is reported, not implied. A different proof
system is a different deployment, with a different `proofSystem()` string and therefore a
different `proofProfile()`.

## The hash scheme

ERC-8274 requires the backend to document how `inputHash` and `outputHash` are built, because two
deployments using different schemes must not be compared. FlashProve's scheme:

```
INPUT_DOMAIN       = "FlashProve/input-v1\0"
input_digest       = SHA-256(INPUT_DOMAIN
                             ‖ u64le(len(policy)) ‖ policy
                             ‖ u64le(len(layout)) ‖ layout
                             ‖ u64le(len(kl))     ‖ kl
                             ‖ u64le(len(key))    ‖ key
                             ‖ u64le(len(entry)) ‖ entry
                             ‖ u32le(entry_number)
                             ‖ u64le(len(request))‖ request
                             ‖ u64le(len(y))      ‖ y
                             ‖ u64le(len(proof))  ‖ proof
                             ‖ u64le(len(id))     ‖ id)
result_v1_digest   = SHA-256(result-v1 line, newline excluded); zero when there is no line
```

Length prefixes keep bytes from moving between two fields without changing the digest, and the
digest does not depend on SP1's stdin encoding: a provider computes it from the files, the guest
computes it from the values it read, and both must agree. Implementation:
`zkvm-prover/fp-pv/src/inputs.rs`; the ten inputs and their order are documented there.

## The FPV1 block

The guest commits 128 raw bytes first, at offset 0 of the SP1 public values:

| offset | size | field |
|---|---|---|
| 0 | 4 | magic `"FPV1"` |
| 4 | 2 | schema version, big-endian, `1` |
| 6 | 2 | reserved, zero |
| 8 | 1 | verdict: 1 YES, 2 WITHIN_LIMITS, 3 NO, 4 NOT_A_VERIFICATION, 5 NOT_CHECKED |
| 9 | 1 | reserved, zero |
| 10 | 2 | call status, big-endian (the call's exit status) |
| 12 | 4 | result-v1 status field, big-endian (0 if absent) |
| 16 | 32 | commitment ID the proof was checked against |
| 48 | 32 | input digest |
| 80 | 32 | result-v1 digest |
| 112 | 16 | reserved, zero |

Fixed offsets and zeroed reserved bytes mean a verdict has exactly one encoding. The decoder is
`src/libraries/FlashProvePublicValues.sol`; the definition is
`zkvm-prover/fp-pv/src/pv.rs`, and the two must change together.

## Layout

```
src/zk/FlashProveZKVerifier.sol             the zk IProofVerifier implementation
src/attestation/FlashProveAttestVerifier.sol the committee IProofVerifier implementation
src/libraries/FlashProvePublicValues.sol  FPV1 decoder (shared: the example reads verdicts from it)
src/interfaces/                           IProofVerifier, IAgentVerifier, IAgentVerifiable,
                                          IERC165, ISP1Verifier
src/examples/ExampleAgentVerifier.sol     one complete IAgentVerifier, for reference
src/mocks/MockSP1Verifier.sol             accepts a placeholder proof; local chains only
test/zk/                                  the zk contract's tests, including the negative controls
test/attestation/                         the committee contract's interface-level tests
test/FlashProvePublicValues.t.sol         FPV1 decoder vectors
script/DeployVerifier.s.sol               deploys FlashProveZKVerifier alone
script/Deploy.s.sol                       deploys it plus one ExampleAgentVerifier
script/AnvilSmoke.s.sol                   the whole zk path against a local anvil
scripts/                                  deploy.sh, anvil-smoke.sh
```

## The attestation path

`FlashProveAttestVerifier` is the committee-backed path: instead of a zk proof, a set of pre-approved
signers attests that a given input produced a given output, and the contract accepts the inference
once `threshold` distinct signers signed the same attestation.

What it fixes at deployment:

- the interface — the same `verify(inputHash, outputHash, metadata, proof)` as the zk path, the
  same `proofSystem()` / `proofProfile()` shape, the same ERC-165 answer;
- deployment configuration — the committee (at most 256 members) and the threshold are constructor
  arguments, validated (empty committee, zero threshold, threshold above the committee, a committee
  above 256, duplicate or zero signer all revert with `InvalidConfiguration()`), and never written
  again, so the instance stays stateless;
- the failure mode — unparseable input returns `false`, never reverts;
- the guards — `metadata` must be 32 bytes, `proof` must be at least `0x80`.

### What a committee member signs

An [EIP-712](https://eips.ethereum.org/EIPS/eip-712) typed-data digest, so wallets and signing
services can display what they sign and a signature is bound to one chain and one deployment:

```
domain       = EIP712Domain(string name, string version, uint256 chainId, address verifyingContract)
               name = "FlashProveAttestVerifier", version = "1",
               chainId = block.chainid, verifyingContract = this deployment
Attestation  = Attestation(bytes32 inputHash, bytes32 outputHash, bytes32 metadataHash)
metadataHash = keccak256(metadata)          // metadata = the 32-byte configuration hash
digest       = keccak256("\x19\x01" ‖ domainSeparator ‖ keccak256(abi.encode(ATTESTATION_TYPEHASH,
                                                                  inputHash, outputHash, metadataHash)))
```

`attestationDigest(inputHash, outputHash, metadataHash)` and `domainSeparator()` return these values,
so a signer can check what it is about to sign against the deployment it targets. The separator is
computed per call: after a chain fork, a signature made for one chain id does not count on the other.

### The proof bundle

```
proof = abi.encode(bytes[] signatures)      // each signature: 65 bytes, r ‖ s ‖ v
```

`verify` decodes the bundle, recovers each signature against the digest above and counts **distinct**
committee members; it answers `true` once the count reaches `threshold`. Order inside the bundle
does not matter. A signature is ignored — never counted, never a revert — when it is not 65 bytes,
has `v` outside {27, 28}, has `s` above secp256k1 n/2 (the malleable twin of a valid signature),
recovers to `address(0)` or to a non-member, or repeats a member already counted. A bundle that
does not decode answers `false`.

### What an attestation does not prove

A committee signature proves *which* input and output the members signed, under which
configuration, for which deployment and chain. It does not prove *when* it was signed: the earliest
time it can be shown to exist is the block of the `IAgentVerifier` call that recorded it. An
application that needs freshness or ordering commits to it inside what is signed — a deadline or
nonce in the task that `inputHash` commits to, or a configuration epoch in `metadata` — rather than
relying on the signature itself.

`test/attestation/FlashProveAttestVerifier.t.sol` covers the threshold (accepted at `threshold`,
rejected one short, 1/1 and 3/3), duplicates counted once, outsiders ignored, binding to input,
output, metadata, deployment and chain id, and the malformed cases above.

## Build and test

```bash
cd contracts
forge test
```

No third-party Solidity dependency is used: the tests define the handful of Foundry cheatcodes
they need in `test/utils/TestBase.sol`.

## The whole path on a local chain

```bash
./scripts/anvil-smoke.sh
```

It reads `config/flashprove.json`, computes the real `FPV1` block with `fp-pv bundle`, deploys the
mock SP1 verifier, `FlashProveZKVerifier` and one `ExampleAgentVerifier`, and calls `verify()` with a
placeholder proof. The proof is not a proof; the call path, the decoding, the commitment / verdict
/ status checks and the digest comparison are all exercised.

## Deploy

```bash
export DEPLOYER_PRIVATE_KEY=...
./scripts/deploy.sh               # only FlashProveZKVerifier
./scripts/deploy.sh --with-example
```

The first form is the one to run against a real chain: one constructor argument, the address of
the SP1 verifier deployed there. The second adds an `ExampleAgentVerifier` so the path can be
walked end to end — that contract is a sample, not part of the shared deployment.

`chain.sp1_verifier` must name the SP1 verifier for the target chain (the Succinct verifier
gateway, or a circuit-specific verifier). The example form reads the remaining parameters — program
vkey, commitment ID, accepted verdicts, status rule, authorized agents — from the configuration
file. The program vkey falls back to `program.vkey_record` when `chain.program_vkey` is absent.

`FlashProveAttestVerifier` takes `(address[] signers, uint256 threshold)` and has no script entry yet:
the committee layout is still being settled, so it is deployed by hand for now.

## Writing your own agent verifier

`src/examples/ExampleAgentVerifier.sol` is the worked example: it binds one `IProofVerifier`, one
program vkey, one commitment ID and an accepted-verdict mask, authorizes a set of agents, consumes
the task ID on success, and lets a failed attempt be retried. Copy the shape, replace the policy.

Three things are yours to decide, not the verifier's: which verdicts count (`YES` alone, or also
`WITHIN_LIMITS`), whether `call_status` must be zero, and which commitment ID this application
accepts.

## What it proves, and what it does not

It proves that a specific proof — bound to a specific program vkey, a specific input digest and a
specific result line — verified under the SP1 verifier this chain trusts, and that the block's
digests equal the two hashes the caller supplied.

It does not prove that the model is the one you wanted, that the inputs are honest, that the
commitment ID belongs to your circuit, or that the task was authorized and paid for. Those are
claims about configuration and context: they belong to the `IAgentVerifier` above this contract,
or to whoever signed the input. See `../docs/proving-readiness.md` for the longer version.
