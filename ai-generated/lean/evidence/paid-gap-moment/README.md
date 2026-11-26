# Paid physical clock-gap moments

The [Lean body](../../RKCert/ReviewedNative/PaidGapMoment.lean)
uses the physical clocks given by the row sums of the tableau.
For their diagonal matrix C, it uses the uncompensated
commutator CA − AC. The weight belongs to the row index, and
the signed gap is the row clock minus the column clock.

For a positive commutator power h, reviewed order through p
pays the denominator-cleared gap moment at every exponent q
with 2h + q + 1 ≤ p. The result is over a field with no
characteristic-zero, triangularity, or distinct-clock premise.
This result is the raw moment identity, not a residue-field
combination, regrouping, or gap-count theorem.

The body and [standalone no-output audit](../../AuditPaidGapMoment.lean)
exited zero with Lean 4.36.0 and the Mathlib pin in
[acceptance.tsv](acceptance.tsv). Six nonfatal linter reports in
private proofs of the unchanged measured body are identified in
the [warning admission](body-warning-admission.tsv). The audit
elaborated three literal clients without warnings, including
the expanded cleared pair sum and the ordinary field reciprocal
form. Its [unmodified output](typed-audit-output.txt) contains
three named checks and three [stock-only axiom reports](actual-axioms.tsv).
The [six reviewed providers](reviewed-providers.sha256) are pinned
by source hash. No compiled objects are included, and no other
Lean version is asserted.
