# Exact topological suffix and last-live vertices

The [Lean body](../../RKCert/ReviewedNative/TopologicalLastLive.lean)
works with a finite directed relation and an injective starting rank
that increases along its edges. For a marked vertex, it constructs
a topological ordering in which the vertices after the mark are
exactly its strict descendants, reached by paths of positive length.

For a chosen live subset, a vertex can be last live precisely when a
topological ordering exists, the vertex is live, and none of its
strict descendants are live. The paths are in the full graph, not
just the live subset. Both results are combinatorial. They do not
claim a minimum index, a tableau adapter, or a pruning theorem.

The exact body exited zero with no diagnostics under Lean 4.36.0
and the pinned Mathlib revision. The separate
[typed audit](../../RKCert/ReviewedNative/TopologicalLastLiveAudit.lean)
also exited zero, used the exact measured body, and emitted no
compiled files. It elaborated two typed clients. The
[raw audit output](typed-audit-output.txt) and
[actual axiom table](actual-axioms.tsv) report only `propext`,
`Classical.choice`, and `Quot.sound` for the two named statements.

The [acceptance ledger](acceptance.tsv) records the actual source,
receipt, object, and stock input fingerprints. The
[12 stock API source hashes](stock-api-sources.sha256) are relative
to the Mathlib source root. The body uses no local project provider.
No compiled artifacts are included here.

For an independent check with the pinned dependencies already available,
run from `ai-generated/lean`:

```sh
lake build +RKCert.ReviewedNative.TopologicalLastLive:olean
lake env lean RKCert/ReviewedNative/TopologicalLastLiveAudit.lean
```
