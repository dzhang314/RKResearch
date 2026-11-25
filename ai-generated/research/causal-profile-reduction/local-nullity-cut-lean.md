# Lean certificates for nodal cuts with mixed diagonals

The [all-order mixed-diagonal cut](../../lean/RKCert/ReviewedNative/LocalVolterraCutNullity.lean) uses the reviewed `HasOrder p A b` over an arbitrary field and requires only a lower triangular tableau. It counts zero diagonal entries only among the stages on the side being bounded. The other side may have any diagonal. The count is zero when the counted block is nonsingular, recovering the previous cutoff.

The [abstract rank identity](../../lean/RKCert/ReviewedNative/NodalMaskNullity.lean) shows that each paid step loses exactly the dimension of the intersection of the current masked space and the kernel of the Volterra map. The [actual column and covector cuts](../../lean/RKCert/ReviewedNative/MixedNodalCut.lean) retain that local bound. First- and last-coordinate pivots then bound the local nullity by the number of zero diagonals in the counted segment.

The three new Lean modules passed independent kernel replay on Lean 4.36.0. See the [mathematical proof](local-nullity-nodal-cut.md) for the closed form and the separate endpoint-mask refinement. The latter is not certified by these three modules.
