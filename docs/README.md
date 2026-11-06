# Reports

The measured records behind this repository. Each is a run log: figures, conditions and what the
run does not cover.

| Report | What it records |
|---|---|
| [cycle-baseline.md](cycle-baseline.md) | SP1 guest execution and the cycle counts of the full verifier run |
| [cycle-optimization.md](cycle-optimization.md) | The compile-level optimization rounds, each with its measured cycle delta |
| [merge-report.md](merge-report.md) | The on-chain side merged into the verifier line, and the full verification chain re-run |
| [proving-readiness.md](proving-readiness.md) | The on-chain side, ready: keys, public values, contracts, prover drivers |

Cycle figures in these reports are measured with SP1's executor. Proof times are derived from the
cycle count and are marked as estimates.
