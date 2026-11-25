# Order twenty: conditional 28-stage chronological cut bound

The [reviewed endpoint](../../RKCert/ReviewedNative/OrderTwentyFourClockCounted28FromOrder.lean)
uses `HasOrder 20 A b` and a lower-triangular matrix. For a cut with a
fixed set of four discarded clocks and trivial intersection of the
counted-side readout with the corresponding Volterra kernel, it gives
at least 28 counted stages. The two precise clock-cover conditions,
for prefix and suffix respectively, are in the
[mathematical statement](../../../research/causal-profile-reduction/multiclock-mask-cut.md#6-a-separate-lean-checked-four-clock-certificate-at-order-20).
Weights and abscissae need not have any particular sign. This is not
an unrestricted ERK or DIRK stage bound.

The [source audit](../../AuditOrderTwentyFourClockCounted28FromOrder.lean)
checks both cut orientations and the underlying transport types. All
twelve [raw axiom reports](typed-axiom-audit.log) contain only the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`.
The [dependency hashes](dependencies.sha256) and
[replay order](replay-order.tsv) identify the checked sources.
The verified toolchain was Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
