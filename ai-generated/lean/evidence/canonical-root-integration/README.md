# End-to-end canonical reduction and full-series uniqueness

[ProfilePrune](../../RKCert/ReviewedNative/CanonicalProfilePrune.lean)
first groups stages with identical full rooted-tree profiles, then
restricts the aggregate matrix and weights to visible coordinates.
The aggregate tree span is full before pruning. The reduction preserves
every raw scalar rooted output and the reviewed `HasOrder` predicate,
and the remaining invisible subspace is zero.

[ReducedUniqueness](../../RKCert/ReviewedNative/CanonicalReducedUniqueness.lean)
shows that principal pruning preserves full tree span in this setting
and compares two reductions. If their original raw scalar outputs agree
on every reviewed tree, one bijection of their surviving stage indices
identifies both reduced matrix entries and weights exactly. The
[end-to-end typed audit](../../AuditCanonicalRootIntegration.lean)
applies this to the chosen profile partitions, including preservation of
reviewed `HasOrder`. Equal `HasOrder` at a fixed classical order is not
the full-series hypothesis. No minimum over tableaux of a fixed
classical order is claimed, and no separate stage-minimum theorem is
stated in these Lean files.

This builds on the separately checked
[coalescer](../canonical-profile-coalesce/README.md),
[visibility and principal restriction](../canonical-visible-prune/README.md),
and [split uniqueness](../canonical-split-uniqueness/README.md). Both
new bodies and the no-output audit exited zero under the Lean and
Mathlib versions pinned in [acceptance.tsv](acceptance.tsv). ProfilePrune
emitted no diagnostics; ReducedUniqueness emitted one nonfatal
deprecation warning. The audit elaborated two typed clients. Its
unmodified [output](typed-audit-output.txt) records six named type checks
and five axiom reports, all using only `propext`, `Classical.choice`,
and `Quot.sound`. The [actual axiom lists](actual-axioms.tsv) and
[24 exact existing project source pins](reviewed-providers.sha256)
are recorded separately. No compiled objects are included.
