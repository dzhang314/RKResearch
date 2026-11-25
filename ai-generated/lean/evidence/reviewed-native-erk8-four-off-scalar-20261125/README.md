# Order-eight ERK four-off scalar endpoint

Import [`RKCert.ReviewedNative.ERK8FourOffScalar`](../../RKCert/ReviewedNative/ERK8FourOffScalar.lean).
In namespace `RKResearch.Certified.Graded.MultiOff.FourOff8Scalar`, the
checked declarations `firstCleanAt4_contradiction` and
`firstCleanAt5_contradiction` are **conditional scalar** results over a
characteristic-zero field. The inputs are three distinct Lobatto clocks,
the specified quadratic shape with nonzero scale and its exact ratio,
and the corresponding finite row equations. The index-4 declaration
uses the extra three first-clean equations; the index-5 declaration uses
the literal zero tap instead. Their moment function is the concrete clean
residue expression, not a freely supplied moment vector.

These declarations do **not** infer those inputs from a Runge–Kutta
tableau. The checked [tagged census](../reviewed-native-erk-order-eight-tagged-census/README.md)
and the [mathematical four-off argument](../../../research/erk-eight-stage-floor/four-off-closure.md)
remain separate. This source does not add a physical four-off exclusion,
a `Fin 10` exclusion, a stage lower bound, or a stage-table change. It
introduces neither the polynomial Ports module nor any proposed native
chronology or row producer.

## Exact warm checks

The exact scalar body and a [separate no-output typed audit](../../AuditReviewedNativeERK8FourOffScalar.lean)
both exited zero under stock Lean 4.36.0 and locked Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The body depends on the locked
external library only: no RK project provider objects were on its path.
The audit elaborated both endpoint types against the successful fresh body
and [reported](typed-audit-output.txt) only `propext`, `Classical.choice`,
and `Quot.sound` for each named declaration. The audit emitted no object.

[Acceptance](acceptance.tsv) records both measured exits, exact source and
raw log hashes, and the relation between raw and published output. The
[body diagnostics](body-diagnostics.txt) contain its 29 lint warnings;
only their source path prefix was replaced with the repository-relative
prefix. The raw audit output is byte-unchanged. The [fragment ledger](stock-fragments.tsv)
records the public/private/server/IR fragments of the single accepted
body, without publishing any compiled objects or execution paths.
The [repair ledger](measured-repair-chain.tsv) pins two prior failed
bodies and raw log hashes: first module-mode visibility for `CharZero`,
then the eleven printed proof sites in the coefficient aliases, trace
alias and denominator clearing. No theorem statement changed during
those repairs.

The certificate package configuration is unchanged at integration base
`adfb669aeb73b02cd807ed863f95707522259805`. This is warm serial body and
external typed-audit evidence, not a cold package build or a separate
`leanchecker` run. For later replay with the pinned tools and dependencies
present, run from the repository root:

```sh
sha256sum -c ai-generated/lean/evidence/reviewed-native-erk8-four-off-scalar-20261125/added-sources.sha256
cd ai-generated/lean
lake build +RKCert.ReviewedNative.ERK8FourOffScalar
lake env lean -j1 -M3000 AuditReviewedNativeERK8FourOffScalar.lean
```
