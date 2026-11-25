# Common-diagonal height cutoff

The [Lean body](../../RKCert/ReviewedNative/CommonDiagonalHeight.lean)
proves that a literal tree column can be matched on all stages of
depth at most a chosen height bound by a linear combination of tree
columns of height at most that bound and of no greater order. The assumptions
apply only to rows within the depth cutoff: those rows have a common
diagonal entry, and every nonzero off-diagonal entry leads to a stage
of strictly smaller depth.

Over a commutative ring, if the weights are supported within the
depth cutoff, checking that the raw scalar outputs vanish through any
fixed order is equivalent to checking only trees within both the
order and height bounds. The body also states this equivalence for
equality of two tableaux whose shallow rows use the same diagonal
value. The sharpness
examples in the [mathematical note](../../../research/canonical-rk-realization/COMMON-DIAGONAL-HEIGHT.md)
are not part of this Lean check.

The body and [no-output typed audit](../../AuditCommonDiagonalHeight.lean)
both exited zero under Lean 4.36.0 and the Mathlib pin in
[acceptance.tsv](acceptance.tsv). The audit elaborated four typed
clients. Its [unmodified output](typed-audit-output.txt) contains
five named type checks and three named reports with only the stock
axioms propext, Classical.choice, and Quot.sound. The
[actual axiom lists](actual-axioms.tsv) and
[eight exact project providers](reviewed-providers.sha256) are recorded
separately. No compiled objects are included.
