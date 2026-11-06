# The on-chain verifier

`FlashProveVerifier` is the deployment. It is a stateless `IProofVerifier` — ERC-8274's inner,
algorithm-specific layer — for FlashProve inference proofs, carried by SP1 (`zk/sp1`).

One instance serves every application. It stores no agent, no task, no commitment ID and no
verdict policy; the program vkey arrives with each call, inside `metadata`. An `IAgentVerifier`
wraps it, keeps the state, and decides which verdicts count as an answer.

```
IAgentVerifiable  ──►  IAgentVerifier  ──►  FlashProveVerifier  ──►  ISP1Verifier
 (settlement)          (application,        (this contract,         (the chain's
                        stateful,           stateless)              SP1 verifier)
                        per app)
```

## The call

```solidity
function verify(
    bytes32 inputHash,       // FPV1 input digest
    bytes32 outputHash,      // FPV1 result-v1 digest
    bytes calldata metadata, // abi.encode(bytes32 programVKey)
    bytes calldata proof     // abi.encode(bytes publicValues, bytes sp1Proof)
) external view returns (bool);
```

`true` requires all three:

1. the SP1 verifier on this chain accepts `sp1Proof` for `programVKey` over `publicValues`;
2. the FPV1 block's `input_digest` equals `inputHash`;
3. the FPV1 block's `result_v1_digest` equals `outputHash`.

A malformed bundle (`metadata` not 32 bytes, `proof` shorter than `0x40`) or any failing step
returns `false`. The contract does not revert on a bad proof: the outer layer is expected to
record the attempt either way, and a revert there would throw the record away.

## What it says about itself

| Call | Value |
|---|---|
| `proofSystem()` | `"zk/sp1"` — the paradigm and variant, per ERC-8274 |
| `proofProfile()` | `keccak256(abi.encode(PROOF_SYSTEM, address(this).codehash))` |
| `supportsInterface` | `IProofVerifier` and `IERC165` |

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
src/FlashProveVerifier.sol                 the IProofVerifier implementation
src/libraries/FlashProvePublicValues.sol  FPV1 decoder
src/interfaces/                           IProofVerifier, IAgentVerifier, IAgentVerifiable,
                                          IERC165, ISP1Verifier
src/examples/ExampleAgentVerifier.sol     one complete IAgentVerifier, for reference
src/mocks/MockSP1Verifier.sol             accepts a placeholder proof; local chains only
test/                                     unit and path tests, including the negative controls
script/DeployVerifier.s.sol               deploys FlashProveVerifier alone
script/Deploy.s.sol                       deploys it plus one ExampleAgentVerifier
script/AnvilSmoke.s.sol                   the whole path against a local anvil
scripts/                                  deploy.sh, anvil-smoke.sh
```

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
mock SP1 verifier, `FlashProveVerifier` and one `ExampleAgentVerifier`, and calls `verify()` with a
placeholder proof. The proof is not a proof; the call path, the decoding, the commitment / verdict
/ status checks and the digest comparison are all exercised.

## Deploy

```bash
export DEPLOYER_PRIVATE_KEY=...
./scripts/deploy.sh               # only FlashProveVerifier
./scripts/deploy.sh --with-example
```

The first form is the one to run against a real chain: one constructor argument, the address of
the SP1 verifier deployed there. The second adds an `ExampleAgentVerifier` so the path can be
walked end to end — that contract is a sample, not part of the shared deployment.

`chain.sp1_verifier` must name the SP1 verifier for the target chain (the Succinct verifier
gateway, or a circuit-specific verifier). The example form reads the remaining parameters — program
vkey, commitment ID, accepted verdicts, status rule, authorized agents — from the configuration
file. The program vkey falls back to `program.vkey_record` when `chain.program_vkey` is absent.

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
