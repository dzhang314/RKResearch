# Endpoint masks cost one order in Lean

The [chronological endpoint cut](../../lean/RKCert/ReviewedNative/EndpointPaidMaskCut.lean) improves the effective order from `p - 2` to `p - 1` when the clocks masked on the discarded side are all zero or all one. For a prefix it counts its physical clocks; for a suffix it counts clocks only at stages with individually nonzero output weight. In either direction the bound charges zero diagonal entries only on the counted side.

The proof applies to the human-reviewed `HasOrder p A b` over any field. It establishes the relevant paid Hankel nonsingularity for the two masks without any positivity assumption or extension of the coefficient field. The [general readout theorem](../../lean/RKCert/ReviewedNative/PaidMaskOneCharge.lean) also permits singular Hankel widths, charging their actual measured ranks, and the [tableau bridge](../../lean/RKCert/ReviewedNative/NodalPaidHankel.lean) supplies both column and weighted-output versions.

The three new modules passed independent kernel replay on Lean 4.36.0. These are local stage-count conditions, not a new unconditional stage floor. See the [paper argument](local-nullity-nodal-cut.md) for the connection with the general nodal cut.
