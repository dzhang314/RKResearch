# Diagonal shift preserves the first differing literal order

The [Lean body](../../RKCert/ReviewedNative/DiagonalTreeShiftOrder.lean)
proves that a literal tree expands to its coefficient-one term plus a
linear combination of trees of strictly smaller order. If two outputs
agree on those smaller orders, the transform adds the same correction
to both values at the fixed tree. With additive cancellation, equality
at that tree is therefore unchanged.

Over a commutative ring, the inverse shift makes agreement through any
chosen order and the first differing order equivalent before and after
translation. The cutoff and first-difference predicates use the
reviewed literal tree's natural order. This certificate has no
matrix support, actual tableau order, or dependency-depth claim.

The body and [no-output typed audit](../../AuditDiagonalTreeShiftOrder.lean)
both exited zero under the Lean and Mathlib pins in [acceptance.tsv](acceptance.tsv).
The audit elaborated five client examples and emitted seven named type checks
and five named axiom reports. The [unmodified output](typed-audit-output.txt)
and [actual axiom lists](actual-axioms.tsv) show only the stock axioms
propext, Classical.choice, and Quot.sound. The
[nine exact project providers](reviewed-providers.sha256), including
the [previously checked core](../diagonal-tree-shift-core-matrix/README.md),
are bound by source hash. No compiled objects are included.
