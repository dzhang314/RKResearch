import RKCert.ReviewedNative.DIRKSmall

#print axioms RKResearch.FiniteRootedTree.order_addBush
#print axioms RKResearch.FiniteRootedTree.forestFactorial_addBush
#print axioms RKResearch.FiniteRootedTree.factorial_addBush
#print axioms RKResearch.FiniteRootedTree.factorial_butcherProduct_cut
#print axioms RKResearch.Φ_addBush
#print axioms RKResearch.Φ_branch_swap
#print axioms RKResearch.HasOrder.factorial_isUnit
#print axioms RKResearch.HasOrder.balanced_root_cut
#print axioms RKResearch.HasOrder.rootStageResidual_pairing
#print axioms RKResearch.HasOrder.bushy_moment
#print axioms RKResearch.HasOrder.natCast_isUnit
#print axioms RKResearch.HasOrder.monomialStageDefect_moment
#print axioms RKResearch.HasOrder.bushy_moment_div
#print axioms RKResearch.map_Φ_coefficients
#print axioms RKResearch.HasOrder.map_coefficients
#print axioms RKResearch.lowerTriangular_mulVec_pivot
#print axioms RKResearch.HasOrder.lower_triangular_of_all_fields
#print axioms RKResearch.HasOrder.unit_diagonal_of_all_fields
#print axioms RKResearch.HasOrder.order_three_stages_field
#print axioms RKResearch.HasOrder.dirk_order_four_stages_field
#print axioms RKResearch.HasOrder.dirk_order_five_stages_field
#print axioms RKResearch.HasOrder.dirk_order_four_stages
#print axioms RKResearch.HasOrder.dirk_order_five_stages

open RKResearch

example {R : Type*} [CommRing R] [Nontrivial R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (ho : HasOrder 5 A b) (ha : A.IsLowerTriangular) : 4 ≤ s :=
  ho.dirk_order_five_stages ha

example {R : Type*} [CommSemiring R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (ho : HasOrder 8 A b) : IsUnit (7 : R) := by
  simpa using ho.natCast_isUnit (n := 7) (by decide) (by decide)
