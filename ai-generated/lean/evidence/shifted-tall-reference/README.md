# Shifted exact-flow reference on tall trees

The [Lean body](../../RKCert/ReviewedNative/ShiftedTallReference.lean)
shows that the literal tree shift is a binomial transform on the tall
trees, indexed by their edge count. Specializing to the exact-flow
target gives a three-term recurrence in characteristic zero. The
recurrence never divides by the shift, and also covers zero shift.
Two consecutive shifted exact-flow values cannot both vanish.

If the tableau with matrix B + γI has reviewed order through p and
n + 2 ≤ p, the matrix B has a nonzero scalar output on at least
one of the two literal tall trees with n and n + 1 edges. This
does not assume triangularity or claim a depth construction or
stage bound.

The body and [standalone no-output audit](../../AuditShiftedTallReference.lean)
exited zero with Lean 4.36.0 and the Mathlib pin in
[acceptance.tsv](acceptance.tsv). Two nonfatal linter diagnostics
on one body tactic are exactly preserved in the
[warning admission](body-warning-admission.tsv); the measured
source was not changed. The audit elaborated four typed clients
without warnings. Its [unmodified output](typed-audit-output.txt)
contains six named checks and five [stock-only axiom reports](actual-axioms.tsv).
The [twelve reviewed providers](reviewed-providers.sha256) are pinned
by source hash. No compiled objects are included, and no other Lean
version is asserted.
