# Split-coordinate visibility and principal pruning

The [Lean body](../../RKCert/ReviewedNative/CanonicalVisiblePrune.lean)
works over a field on the actual finite split coordinate tableau. A
directed path along nonzero matrix entries to a nonzero weight supplies
a one-hole context that reads the starting coordinate times a nonzero
scalar. The invisible space is the largest ideal invariant under the
tableau action and killed by the output. It consists exactly of the
vectors that vanish at every visible coordinate.

Pruning takes the principal submatrix on visible indices and restricts
the weights. Every reviewed rooted-tree stage column restricts to the
corresponding pruned column, every raw rooted output is unchanged, and
the reviewed `HasOrder` predicate is preserved in both directions.
Every remaining index is visible. The statement concerns split
coordinates; applying it to a nontrivial profile quotient first requires
a separate coalescing proof. This certificate does not yet formalize
coalescence, full-series minimality, or uniqueness.

The body and its independent [typed audit](../../AuditCanonicalVisiblePruneOnly.lean)
both exited zero under Lean 4.36.0 with Mathlib at
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The body emitted nonfatal
lint warnings. The [measured identities](acceptance.tsv) record the
source, log, and body artifact digests. The unmodified
[typed audit output](typed-audit-output.txt) records eight type probes
and eight axiom reports, using only the three standard Lean axioms
listed in [actual-axioms.tsv](actual-axioms.tsv). The audit also
elaborates seven concrete typed clients. The exact six pre-existing
project sources are listed in [reviewed-providers.sha256](reviewed-providers.sha256).
No compiled objects are included in this evidence.
