# Topological reindexing of a tableau

The [Lean body](../../RKCert/ReviewedNative/TopologicalReindex.lean)
contains two equivalences for an actual ranking `σ : V ≃ Fin n`:

* The reindexed matrix `Matrix.reindex σ σ A` is strictly lower
  triangular exactly when `σ` takes each nonzero edge
  `u → v` (meaning `A v u ≠ 0`) from an earlier column to a
  later row. This equivalence needs only a zero in the coefficient type.
* The literal `LastActive` predicate for the inverse-reindexed weights
  at `σ t` is equivalent to nonzero original weight at `t` and zero
  original weight at every strictly later rank. This equivalence uses
  the existing field-valued `LastActive` predicate.

Neither statement assumes nonzero or positive weights elsewhere.
They do not assert pruning, an attainable index interval, or a stage
bound.

The exact body exited zero without diagnostics. The separate
[typed audit](../../RKCert/ReviewedNative/TopologicalReindexAudit.lean)
also exited zero, with two typed clients and no freshly emitted
compiled objects. In its [raw report](typed-audit-output.txt) and
[actual axiom table](actual-axioms.tsv), the strictness equivalence uses
`propext`, `Classical.choice`, and `Quot.sound`; the literal
`LastActive` equivalence uses only `propext` and `Quot.sound`.

The [acceptance ledger](acceptance.tsv) identifies the measured input
and object fingerprints. The [reviewed source manifest](reviewed-providers.sha256)
covers both direct providers, `TopologicalLastLive` and
`EndpointAdjoint`, and all their recursively reached project sources,
not the stock Mathlib import cone. No compiled artifacts are included.

For an independent check with the pinned Lean 4.36.0 and Mathlib
dependencies available, run from `ai-generated/lean`:

```sh
lake build +RKCert.ReviewedNative.TopologicalReindex:olean
lake env lean RKCert/ReviewedNative/TopologicalReindexAudit.lean
```
