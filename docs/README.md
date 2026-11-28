# Reports

The measured records behind this repository. Each is a run log: figures, conditions and what the
run does not cover.

| Report | What it records |
|---|---|
| [flashprove-to-onchain.md](flashprove-to-onchain.md) | A short visual guide from a FlashProve proof to local on-chain verification |
| [cycle-baseline.md](cycle-baseline.md) | SP1 guest execution and the cycle counts of the full verifier run |
| [cycle-optimization.md](cycle-optimization.md) | The compile-level optimization rounds, each with its measured cycle delta |
| [merge-report.md](merge-report.md) | The on-chain side merged into the verifier line, and the full verification chain re-run |
| [proving-readiness.md](proving-readiness.md) | The on-chain side, ready: keys, public values, contracts, prover drivers |
| [end-to-end-cpu-groth16.md](end-to-end-cpu-groth16.md) | The completed accepted CPU Groth16 run: identity, six gates, artifacts, local on-chain closure and limits |
| [evidence-record.md](evidence-record.md) | Sanitized public record of the accepted run: hashes, local receipts and the verification matrix |

The evidence record is a factual summary, not the full raw evidence.

Cycle figures in these reports are measured with SP1's executor. Proof times in the older
reports are derived from the cycle count and are marked as estimates; the CPU Groth16 report
records a measured proof run.
