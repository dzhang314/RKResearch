# Coalescing exact rooted stage profiles

The [Lean body](../../RKCert/ReviewedNative/CanonicalProfileCoalesce.lean)
partitions a finite stage tableau over a field by equality on every
literal rooted-tree stage column. The full stage-column span is
exactly the subspace constant on these classes. Row sums into a fixed
class are independent of the representative, so they give actual
aggregate matrix entries; each new output weight is the sum of the
old weights in its class. Every literal stage column pulls back along
the class label map, and every raw scalar rooted output is preserved.
The reviewed `HasOrder` predicate is therefore equivalent for every
order before and after coalescing.

The [typed audit](../../AuditCanonicalProfileCoalesceOnly.lean) also
checks that the full stage-column span has dimension equal to the
class count. The chosen labels have no claimed chronological order.
This certificate does not prune invisible classes, establish that
the resulting tableau is minimal, or verify the reduced uniqueness
adapter.

The body and no-output audit both exited zero under Lean 4.36.0 and the
Mathlib pin recorded in [acceptance.tsv](acceptance.tsv). The body
emitted two nonfatal deprecation warnings. The audit elaborated eight
typed clients. Its unmodified [output](typed-audit-output.txt) has
eight named type checks and eight reports containing only the standard
Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
[Actual axiom lists](actual-axioms.tsv) and
[the 21 exact project provider sources](reviewed-providers.sha256)
are recorded separately. No compiled objects are included.
