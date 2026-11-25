# Split-tableau uniqueness from the full rooted series

The [Lean body](../../RKCert/ReviewedNative/CanonicalSplitUniqueness.lean)
compares two finite stage tableaux over the same field. It assumes that
their scalar outputs agree on every reviewed rooted tree, that the stage
columns span the whole coordinate space for each tableau, and that both
context-invisible subspaces are zero. It produces one stage equivalence
`e : κ ≃ ι` with exact coefficients `B j k = A (e j) (e k)` and exact
weights `d j = b (e j)`. This is literal reindexing, not just linear
similarity. A finite initial segment of the rooted series is not a
premise.

The comparison uses the span of pairs of literal tree columns and
one-hole contexts whose multipliers are tree columns. Together with the
[visibility certificate](../canonical-visible-prune/README.md), it
addresses already split coordinates. It does not construct a quotient
of an arbitrary tableau or certify profile coalescence, the reduced
adapter, or the full canonical-minimal realization theorem.

The body and the independent [typed audit](../../AuditCanonicalSplitUniquenessOnly.lean)
both exited zero under Lean 4.36.0 and the Mathlib pin in
[acceptance.tsv](acceptance.tsv). The body emitted two nonfatal lint
warnings. The audit emitted no object and elaborated four typed clients,
including the literal coefficient and weight identities above.
Its unmodified [output](typed-audit-output.txt) records eight named type
checks and four reports containing only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`.
[Actual axioms](actual-axioms.tsv) and the nine exact
[project provider sources](reviewed-providers.sha256) are recorded
separately. No compiled objects are included.
