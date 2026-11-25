import RKCert.ReviewedNative.SDIRK118AlgebraicWitness

open RKResearch
open RKResearch.Certified.PaidDefectBridge.SDIRK118

example : ∃ F : IntermediateField ℚ ℝ, Algebra.IsAlgebraic ℚ F ∧
    ∃ (A : Matrix (Fin 11) (Fin 11) F) (b : Fin 11 → F) (γ : F),
      0 < γ ∧ A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ HasOrder 8 A b :=
  exists_strict_sdirk11_hasOrder8_over_algebraic_field

#print axioms exists_strict_sdirk11_hasOrder8_over_algebraic_field
#print axioms Subfield.literal_lift_seedCoefficientField
#print axioms Subfield.literal_coefficients_mem
#print axioms Subfield.literal_coefficients_isAlgebraic
#print axioms Subfield.exact_seed_isAlgebraic

example : ∃ F : IntermediateField ℚ ℝ, FiniteDimensional ℚ F ∧ Module.finrank ℚ F ≤ 12 ∧
    ∃ (A : Matrix (Fin 11) (Fin 11) F) (b : Fin 11 → F) (γ : F),
      0 < γ ∧ A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ HasOrder 8 A b :=
  exists_strict_sdirk11_hasOrder8_over_field_degree_le_twelve

#print axioms exists_strict_sdirk11_hasOrder8_over_field_degree_le_twelve
#print axioms Subfield.seedCoefficientField_finite_degree
#print axioms Subfield.literal_lift_finite_degree
