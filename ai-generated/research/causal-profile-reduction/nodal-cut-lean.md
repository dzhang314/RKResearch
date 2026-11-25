# Lean certificates for the all-order nodal cutoff

The [mathematical statement and proof](nodal-cut-recurrence.md) now have native certificates over fields. The chronological bound uses the human-reviewed `HasOrder p A b` and requires a lower triangular tableau with nonzero diagonal. It imposes no sign, stage-minimality or nonzero-output-weight assumptions. The effective order for a segment with `q` relevant clocks is `p - 2*q`, for positive effective order.

* [NonsingularNodalCut.lean](../../lean/RKCert/ReviewedNative/NonsingularNodalCut.lean): both chronological directions, and an invariant coordinate-subspace form.
* [NodalMaskFamily.lean](../../lean/RKCert/ReviewedNative/NodalMaskFamily.lean): the original masked columns and rows are linearly independent, including the indexing of each family.
* [NodalMaskParity.lean](../../lean/RKCert/ReviewedNative/NodalMaskParity.lean): a shared proof for the two directions. It compares each masked polynomial space with a wider space whose independence is already supplied by the order. At equality the masked space is the whole target.
* [NonsingularDualCensus.lean](../../lean/RKCert/ReviewedNative/NonsingularDualCensus.lean): exact parity ranks for the actual iterated output rows, including zero weights.

The six new modules compiled and passed independent kernel replay on Lean 4.36.0 with the pinned Mathlib. All seven audited output declarations depend only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
