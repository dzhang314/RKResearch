# Diagonal shift on literal rooted trees

The [core](../../RKCert/ReviewedNative/DiagonalTreeShift.lean) works in the
free linear span of the reviewed literal ordered trees. Each recursive
graft either keeps the new edge or contracts it with the shift coefficient.
Shifts compose by adding their coefficients; over a commutative ring,
negating the coefficient gives the inverse in both directions.

The [matrix theorem](../../RKCert/ReviewedNative/DiagonalTreeShiftMatrix.lean)
identifies evaluation of that expansion with adding the same scalar
multiple of the identity to the tableau matrix. It applies to both
the stage column and the weighted scalar output over a commutative
semiring, with no stage ordering or support hypothesis. No order
cutoff, first-failure, or dependency-depth claim is included here.

Both bodies and the [no-output typed audit](../../AuditDiagonalTreeShiftCoreMatrix.lean)
exited zero under the Lean and Mathlib pins in [acceptance.tsv](acceptance.tsv).
The audit elaborated six client examples, including the first-edge coefficient
in the matrix API, and emitted nine named type checks and nine named axiom
reports. The [unmodified output](typed-audit-output.txt) and
[actual axiom lists](actual-axioms.tsv) show only the stock axioms
propext, Classical.choice, and Quot.sound. The
[five reviewed providers](reviewed-providers.sha256) are recorded by
source hash. No compiled objects are included.
