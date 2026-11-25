# Exact order-eight strict SDIRK over the rationals, in 15 stages

The reviewed theorem
[`RKResearch.Certified.exists_fifteen_stage_rational_strictSDIRK_exact_eight`](../../RKCert/ReviewedNative/RationalStrictSDIRKFifteenStageEightUpper.lean)
constructs `A : Matrix (Fin 15) (Fin 15) ℚ` and `b : Fin 15 → ℚ`.
It proves that `A` is lower triangular with common nonzero diagonal
`1/8`, with `HasOrder 8 A b` and `¬ HasOrder 9 A b`. The raw coefficients
are in [Core](../../RKCert/ReviewedNative/RationalStrictSDIRKFifteenStageEightCore.lean).
The ninth tall-tree weight is exactly `189383/63417876480`, rather than
`1/362880`. There is no minimum, stability, or node restriction claim.
This is a rational upper witness distinct from the 11-stage real-algebraic
witness; the real-algebraic upper count does not change.

## Checked source and evidence

- The checked closure comprises the literal Core, Tall,
  42 paid batches, and the Upper theorem, plus the standalone
  [typed and axiom audit](../../AuditReviewedRationalStrictSDIRKFifteenStageEightUpper.lean).
  The verification transports 83 closed list checks and 75 exact joins
  over all 626 ordered reviewed tree expressions in orders one through eight.
- [Frozen build order](replay-order.tsv), [exact new source hashes](input.sources.sha256),
  and [five existing source providers](reviewed-providers.sha256) identify
  the complete project closure. The standard Mathlib dependency is pinned
  by the repository manifests (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`).
- On [Lean 4.36.0](toolchain.txt), four exact [pilot modules](pilot-results.tsv)
  were reused and the [continuation](continuation-status.tsv) completed all
  40 remaining batches, the theorem, and the unchanged typed audit. The
  [terminal receipt](terminal.txt) and [raw audit output](audit-output.txt)
  record those checks. The four named theorem axiom reports contain only
  `propext`, `Classical.choice` and `Quot.sound`. The historical raw
  audit output is unedited (only its published filename differs).

## Replay

From `ai-generated/lean`, using the existing pinned Lean/Mathlib and a
separate build workspace:

```sh
receipt=evidence/reviewed-native-rational-sdirk-fifteen-stage-eight-20261125
sha256sum -c "$receipt/input.sources.sha256"
(cd ../.. && sha256sum -c "ai-generated/lean/$receipt/reviewed-providers.sha256")
lake build +RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightUpper
lake env lean -j1 -M1800 -s65536 AuditReviewedRationalStrictSDIRKFifteenStageEightUpper.lean
```

The historical checked run compiled one module at a time with one Lean
thread. On a memory-constrained machine, build the module targets
individually in `replay-order.tsv` before running the last (standalone
source audit) row, rather than scheduling the 42 siblings together.
No compiled objects are required as publication files.
