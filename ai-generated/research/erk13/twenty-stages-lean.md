# The twenty-stage lower bound for order thirteen in Lean

**Theorem.** Over every field of characteristic zero, a strictly lower triangular Runge–Kutta tableau satisfying the reviewed rooted-tree order conditions through order thirteen has at least twenty stages.

The [Lean theorem](../../lean/RKCert/ReviewedNative/ERK13NativeTwentyStages.lean) uses the human-reviewed predicate `HasOrder 13 A b` and has no assumptions on weights, nodes, timing or scalar ports. The [audit](../../lean/AuditReviewedNativeERK13TwentyStages.lean) restates its public signature and prints its axiom dependencies. The [mathematical proof](order-thirteen-twenty-stages.md) gives the full argument in prose.

The existing native stage floor first reduces the problem to nineteen stages. A nonzero first reflected seed already gives a contradiction; otherwise the verified late exclusion pays the actual terminal coordinate by degree seven. This leaves two possible first-escape polynomial degrees. The [degree-six proof](one-early-cut-lean.md) uses the complementary Lobatto factor. For degree seven, [the final chart](../../lean/RKCert/ReviewedNative/ERK13NativePencilQuarticPorts.lean) resolves the high-leading class case and derives the exact original cubic and quartic primitive equations for the other cases. The [cubic](../../lean/RKCert/ReviewedNative/ERK13NativePencilScalarCubic.lean) and [quartic](../../lean/RKCert/ReviewedNative/ERK13NativePencilScalarQuartic.lean) scalar adapters each discharge those equations over the original field.

The scalar proof uses polynomial identities over the integers and finite-field identities modulo 1009. The finite-field checks are polynomial identities, not sampling of stage abscissae. Small named Horner checkpoints keep the literal certificate within the kernel's memory limit. The coefficient reductions and resultant argument are internal to Lean; there is no assumption that a tableau or its abscissae can be reduced modulo 1009.

Verified on Lean 4.36.0 with the pinned Mathlib: the dependency build passed, fourteen selected modules passed independent kernel replay, and the final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
