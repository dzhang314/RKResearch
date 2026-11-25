# At least 25 stages for explicit order sixteen over ordered fields

[The Lean theorem](../../RKCert/ReviewedNative/ERKOrder16OrderedStageFloor25.lean)
states that if `A : Matrix (Fin s) (Fin s) K` is strictly lower triangular
and the tableau satisfies the reviewed `RKResearch.HasOrder 16 A b`,
then `25 ≤ s`. Here `K` is any ordered field, not necessarily the reals.
The module also states the width-24 impossibility separately. Neither
theorem assumes distinct abscissae, signs for the weights, or any
extra hypothesis on the stage defects.

The proof combines the weak-four and weak-five reductions. It verifies
the two remaining weak-five cases separately: the actual sole-inner
case and the actual three-interior case. The latter uses the exact
finite strip and port data; all 51 strip and 51 port shards were
checked. The final Lean theorem uses those checked cases rather than
taking them as hypotheses. This is a lower bound, not a claim that
25 stages suffice.

## Replay evidence

The [complete project source hashes](dependencies.sha256) and
[topological order](replay-order.tsv) include both newly archived
dependencies and the existing reviewed providers actually used.
The [named audit](../../AuditReviewedNativeERK16OrderedStageFloor25.lean)
independently checks the width-24 and all-width statements at their
full reviewed types. Its [output](typed-axiom-audit.log) records only
`propext`, `Classical.choice`, and `Quot.sound` for the two branch
results and both final theorems.

The checked run used Lean 4.36.0 (commit
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`) and Mathlib revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. From the repository root,
verify the source hashes before replay:

```sh
sha256sum -c ai-generated/lean/evidence/erk16-ordered-stage-floor25/dependencies.sha256
cd ai-generated/lean
lake build +RKCert.ReviewedNative.ERKOrder16OrderedStageFloor25
lake env lean -j1 -M3000 AuditReviewedNativeERK16OrderedStageFloor25.lean
```

The checked run built the modules serially. For a memory-constrained
replay, use the recorded order to build individual package targets.
No compiled objects are included in the archive.
