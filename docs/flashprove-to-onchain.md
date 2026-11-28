# From FlashProve to on-chain verification

This example takes a FlashProve inference proof, verifies it inside SP1, and produces a Groth16
proof that an Ethereum contract can verify. The recorded run used a CPU and a local Anvil chain.

```text
  FlashProve proof + inputs
              |
              v
  +------------------------------+
  | Rust FlashProve verifier     |
  | runs inside the SP1 zkVM     |
  +------------------------------+
              |
              v
  +------------------------------+
  | SP1 proves and compresses    |
  | the verifier's execution     |
  +------------------------------+
              |
              v
    Groth16 proof + public values
              |
              v
  +------------------------------+
  | On-chain verification        |
  |                              |
  | SP1 verifier checks the proof |
  | FlashProve contracts check   |
  | the result and task policy   |
  +------------------------------+
              |
              v
       Accepted or rejected
```


## 1. FlashProve proof

The starting point is the accepted FlashProve example: an inference proof and its associated
inputs. The proof is an input to our Rust verifier.

| File | Where | SHA-256 |
|---|---|---|
| FlashProve `example.proof` | [Proof file](../rust-verifier/fixtures/example.proof) | `5ed47fd101093e826a5bc833e57633e5a9237b49213c8f37cf518a3c1c8d9d99` |
| Input manifest | [Inputs and their hashes](../config/input-manifest.json) | `02c865f1589ec40e359142cb10adc0e614e7b397ec1320d5cc70bacb2f64b1fd` |

## 2. Verify in SP1 and produce a Groth16 proof

**Input:** the FlashProve proof and inputs from stage 1. This project's
[Rust FlashProve verifier](../rust-verifier/) checks the original proof. Its `no_std` core is
compiled into the [SP1 guest](../zkvm-prover/guest/), producing a guest ELF that runs in the zkVM.
SP1 proves and compresses that execution, then produces a Groth16 proof.

**Output:** the proof and the guest's public values, including the verdict and input/output
digests. The guest ELF identifies the program being proved; its matching SP1 program vkey is
`0x00077170f863a7960a725e58df8b8f3d111e58468d7d987618983ce1dc1a8f00`.

| File | Where | SHA-256 |
|---|---|---|
| Guest ELF | [v1.0.0](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/flashprove-guest-f31e45a8.elf) | `f31e45a8e29cb63182045517291262422cf86692f02d1989ab7b04d1b74b860b` |
| `proof.bin` — complete SP1 proof | [v1.0.0](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/proof.bin) | `10464eba34f906fdbd75b5a0d1d3bdb8a8406141f774de5fbb704a35f87027d8` |
| `proof.bytes` — Groth16 proof | [v1.0.0](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/proof.bytes) | `f75d969982f1652de7f6763ac7b88e4a02f080bf23f800fcb7d9dde5643c18d7` |
| `public_values.bin` — guest output | [v1.0.0](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/public_values.bin) | `1f0bdac6c80e21bece7454bf22459bb1e3e96a1830e6c77bdfa494abd07c12ef` |

## 3. Verify on-chain

**Input:** `bundle.bin` contains the Groth16 proof and public values. The call also supplies the
input/output digests; the verifier uses the matching program vkey. The
[FlashProveZKVerifier](https://github.com/trustless-ai/flashprove-onchain-verifier/blob/v1.0.0/contracts/src/zk/FlashProveZKVerifier.sol) calls the
[official SP1 Groth16 verifier](https://github.com/succinctlabs/sp1-contracts/blob/2ac5ecbbe473421a963d67e55f182e9a36576f7c/contracts/src/v6.1.0/SP1VerifierGroth16.sol)
and checks the digests. The [example agent contract](https://github.com/trustless-ai/flashprove-onchain-verifier/blob/v1.0.0/contracts/src/examples/ExampleAgentVerifier.sol)
checks task authorization, result policy, and task reuse.

**Output:** accepted or rejected. On the local Anvil chain, the valid bundle was accepted and
the task marked used; changed proof bytes, changed public values, and a repeat were rejected.
The guest result was `verdict=YES`, `call_status=0`. This was not a public-network deployment.

| File | Where | SHA-256 |
|---|---|---|
| `bundle.bin` — encoded proof and public values | [v1.0.0](https://github.com/trustless-ai/flashprove-onchain-verifier/releases/download/v1.0.0/bundle.bin) | `14c06322317057887f6b464919bae2f8b32b4acdd8869905be61a2320c0ae07a` |
| `FlashProveZKVerifier.sol` | [Contract source](https://github.com/trustless-ai/flashprove-onchain-verifier/blob/v1.0.0/contracts/src/zk/FlashProveZKVerifier.sol) | `6cb86c34c4803e1d0440717ff1afcb0983d14361d9a7153a0229df2debe5c66f` |
| `ExampleAgentVerifier.sol` | [Contract source](https://github.com/trustless-ai/flashprove-onchain-verifier/blob/v1.0.0/contracts/src/examples/ExampleAgentVerifier.sol) | `045b66945888f55b43479d49bd0fb6afcaaf0c923b6262bb7b434efe5e89179c` |

These contract hashes identify the source files, not deployed bytecode. Local addresses,
transaction hashes and the result matrix are in the [evidence record](evidence-record.md).

## Try it

Check the artifact hashes, deploy the verifiers to a local Anvil chain and submit the bundle. For the full commands and prerequisites, see the
[end-to-end CPU Groth16 report](end-to-end-cpu-groth16.md). Rebuilding the guest may produce a
different ELF and program identity.
