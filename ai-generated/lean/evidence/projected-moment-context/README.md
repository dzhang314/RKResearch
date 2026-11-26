# Projected polynomial moments on the paid context board

The [Lean body](../../RKCert/ReviewedNative/ProjectedMomentContext.lean)
starts with a projection from the polynomial algebra to a commutative
algebra over a field and a choice of polynomial representatives.
It assumes that reduction does not increase degree and preserves the
formal unit-interval moment below the chosen order. Formal integration
by parts uses only the positive integer denominators up to that order.

Under those hypotheses, the projected model satisfies the reviewed
order condition on every paid literal tree. Inserting a tree in any
one-hole context therefore gives its exact normalized coefficient
whenever the inserted tree is within the paid order. This is a
conditional transfer theorem: it neither constructs a suitable
quotient nor produces a split coordinate tableau or a stage bound.

The body and the [standalone no-output audit](../../AuditProjectedMomentContext.lean)
exited zero with Lean 4.36.0 and the Mathlib pin in
[acceptance.tsv](acceptance.tsv). The one existing body linter warning
is recorded in the [warning admission](body-warning-admission.tsv);
the source was left as measured. The audit had no warnings and
elaborated five field-generic clients. Its [unmodified output](typed-audit-output.txt)
includes eight named checks and five [stock-only axiom reports](actual-axioms.tsv).
The [thirteen exact reviewed providers](reviewed-providers.sha256)
are pinned by source hash. No compiled objects are included, and no
other Lean release is asserted.
