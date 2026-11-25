# Diagonal shift and literal Runge–Kutta order

The [Lean body](../../RKCert/ReviewedNative/DiagonalTreeShiftHasOrder.lean)
relates the reviewed denominator-cleared order conditions to the
normalized exact-flow target, the inverse of each literal tree's
factorial. That factorial is positive and its cast is nonzero in a
characteristic-zero field.

To test the tableau obtained by adding a scalar multiple of the
identity to a matrix, compare the original matrix output with the
exact-flow target shifted by the opposite coefficient. These are
equivalent through any chosen order. The opposite shift on the target
is essential: this is not ordinary Runge–Kutta order of the unshifted
matrix. The body also transports the first differing literal order.
There is no stage-support or dependency-depth condition.

The body and [no-output typed audit](../../AuditDiagonalTreeShiftHasOrder.lean)
both exited zero under the Lean and Mathlib pins in [acceptance.tsv](acceptance.tsv).
The body emitted one nonfatal warning about a redundant change tactic and
is preserved unchanged. The audit elaborated three client examples and
emitted three named type checks and two named axiom reports.
Its [unmodified output](typed-audit-output.txt) and
[actual axiom lists](actual-axioms.tsv) show only the stock axioms
propext, Classical.choice, and Quot.sound. The
[eleven exact project providers](reviewed-providers.sha256), including the
[checked literal order transport](../diagonal-tree-shift-order/README.md),
are bound by source hash. No compiled objects are included.
