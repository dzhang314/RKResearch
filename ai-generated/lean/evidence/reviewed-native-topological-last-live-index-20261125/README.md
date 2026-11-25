# Minimum attainable last-live index

The [Lean body](../../RKCert/ReviewedNative/TopologicalLastLiveIndex.lean)
works with a finite directed relation and an existing topological
ordering. A given set is realizable as the exact strict prefix of a
marked vertex precisely when it omits the mark, is closed under
predecessors, and contains all immediate predecessors of the mark.

For nonempty live support, the least possible zero-based index of
the last live vertex is the cardinality of the predecessor closure
of the live set, minus one. The closure includes the live vertices
themselves and has no restriction on the intermediate vertices of a
path. The result is purely combinatorial. It does not give a
fixed-vertex interval, tableau adapter, or pruning theorem.

The exact body exited zero without diagnostics under Lean 4.36.0
and pinned Mathlib. The separate
[typed audit](../../RKCert/ReviewedNative/TopologicalLastLiveIndexAudit.lean)
also exited zero, used the measured body and its sole project
predecessor, and emitted no compiled artifacts. Its two typed clients
check the exact prefix equivalence and the global `IsLeast` theorem.
The [raw report](typed-audit-output.txt) and
[actual axiom table](actual-axioms.tsv) show only `propext`,
`Classical.choice`, and `Quot.sound` for those two names.

The [acceptance ledger](acceptance.tsv) records the measured input
and output fingerprints. The [sole reviewed source provider](reviewed-providers.sha256)
is the exact existing [suffix theorem module](../../RKCert/ReviewedNative/TopologicalLastLive.lean).
No compiled artifacts are included.

For an independent check with the pinned dependencies available,
run from `ai-generated/lean`:

```sh
lake build +RKCert.ReviewedNative.TopologicalLastLiveIndex:olean
lake env lean RKCert/ReviewedNative/TopologicalLastLiveIndexAudit.lean
```
