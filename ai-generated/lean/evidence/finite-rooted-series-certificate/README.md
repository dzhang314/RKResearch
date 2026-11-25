# A finite certificate for literal rooted-series comparison

The [Lean body](../../RKCert/ReviewedNative/FiniteRootedSeriesCertificate.lean)
accepts a finite list of literal tree columns and span-membership
certificates for the leaf, unary root extensions, and root joins.
Each membership is paid at its own order bound. The resulting
prefix span is exactly the span of all reviewed tree columns within
that bound. If the certified readout vanishes on every order
strictly below a literal nonzero witness, the witness's order is
the smallest possible. If all operations on the list are paid,
then the readout vanishes on the entire rooted series exactly
when it vanishes on the list.

This is certificate soundness, not an implementation of a search
or a checker for arbitrary field arithmetic. The Lean statement
uses one raw scalar readout over a commutative semiring. Comparing
two tableaux can use their block diagonal matrix with the signed
difference row over a ring. The separately supplied
[common-diagonal height note](../../../research/canonical-rk-realization/COMMON-DIAGONAL-HEIGHT.md)
is a mathematical proof, not a theorem formalized by this module.

The body and [no-output typed audit](../../AuditFiniteRootedSeriesCertificate.lean)
both exited zero under Lean 4.36.0 and the Mathlib pin in
[acceptance.tsv](acceptance.tsv). The audit elaborated five typed
clients, including a nonzero leaf with an empty earlier prefix.
Its unmodified [output](typed-audit-output.txt) contains six named
type checks and four named axiom reports, each using only
`propext`, `Classical.choice`, and `Quot.sound`.
[Actual axiom lists](actual-axioms.tsv) and the
[seven exact project providers](reviewed-providers.sha256) are
recorded separately. No compiled objects are included.
