# FlashProve contracts (ERC-8274)

Two layers, as ERC-8274 specifies:

```
Settlement contract (IAgentVerifiable)
  └── FlashProveAgentVerifier   (IAgentVerifier, stateful, application policy)
        └── SP1ProofVerifier    (IProofVerifier, stateless, zk/sp1)
              └── ISP1Verifier  (the deployed SP1 verifier; a mock in local tests)
```

- `src/interfaces/` — the three ERC-8274 interfaces, `IERC165`, and the SP1 verifier interface
  vendored from `succinctlabs/sp1-contracts` v6.1.0 (the release matching circuit v6.1.0).
- `src/libraries/FlashProvePublicValues.sol` — the on-chain decoder for the `FPV1` block that the
  guest commits first. Its layout is defined by `zkvm/fp-pv/src/pv.rs`; both must change together.
- `src/SP1ProofVerifier.sol` — decodes `metadata = abi.encode(bytes32 programVKey)` and
  `proof = abi.encode(bytes publicValues, bytes sp1Proof)`, calls the SP1 verifier, and requires
  the block's input/result digests to equal the caller's `inputHash`/`outputHash`.
- `src/FlashProveAgentVerifier.sol` — binds the commitment ID, the accepted-verdict mask, the
  status rule, the authorized agents and the program vkey; it consumes a task on success, emits
  `VerificationCompleted` on every call and returns the ERC-8274 `verificationDigest`.
- `src/mocks/MockSP1Verifier.sol` — accepts a placeholder proof whose first four bytes are
  `FP-P`. **Not for production.**

## Build and test

```sh
cd zkvm/contracts
forge test
```

No third-party Solidity dependency is used: the tests define the handful of Foundry cheatcodes
they need in `test/utils/TestBase.sol`.

## Local end-to-end call path (anvil)

```sh
zkvm/scripts/anvil-smoke.sh
```

It reads `zkvm/config/flashprove.json`, computes the real `FPV1` block with `fp-pv bundle`,
deploys the mock SP1 verifier + `SP1ProofVerifier` + `FlashProveAgentVerifier` to a local anvil,
and calls `verify()` with a placeholder proof. The proof is not a proof; the call path, the
public-values decoding, the commitment/verdict/status checks and the digest are exercised.

## Deployment

```sh
CONFIG=zkvm/config/flashprove.json DEPLOYER_PRIVATE_KEY=... zkvm/scripts/deploy.sh
```

`chain.sp1_verifier` must name the deployed SP1 verifier for the target chain (the Succinct
verifier gateway, or a circuit-specific verifier). Every other parameter — program vkey,
commitment ID, accepted verdicts, status rule, authorized agents — comes from the configuration
file. The program vkey falls back to `program.vkey_record` when `chain.program_vkey` is absent.

## What the wrapper does and does not prove

The wrapper proves that the SP1 circuit, for the configured program vkey, produced a public-values
block that names the commitment ID, an accepted verdict and the caller's input/output digests. It
does not prove that the model's weights are hidden, nor that the input is legitimate; see
`guide/weight-hiding.md` and `docs/s6b-report.md`.
