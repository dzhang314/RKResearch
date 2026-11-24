import RKCert.ReviewedNative.BooleDIRK56

open RKResearch RKResearch.Certified

example :
    HasOrder BooleDIRK56.A BooleDIRK56.b 6 ∧
      ¬ ∃ γ : ℚ, ∀ i, BooleDIRK56.A i i = γ :=
  ⟨BooleDIRK56.order_six,BooleDIRK56.diagonal_not_constant⟩

example (K : Type*) [Field K] [CharZero K] :
    ∃ (A : Matrix (Fin 5) (Fin 5) K) (b : Fin 5 → K),
      A.IsLowerTriangular ∧ HasOrder A b 6 ∧ ¬ HasOrder A b 7 :=
  BooleDIRK56.exists_exact_order_six

example (K : Type*) [Field K] [CharZero K] :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K),
      A.IsLowerTriangular ∧ HasOrder A b 6} 5 :=
  dirk_order_six_isLeast_charZero_field K

#print axioms checkScaledOrder_spec
#print axioms hasOrder_of_scaled_moments
#print axioms hasOrder_of_scaled_check
#print axioms BooleDIRK56.order_six
#print axioms BooleDIRK56.diagonal_not_constant
#print axioms BooleDIRK56.not_order_seven_map
#print axioms BooleDIRK56.exists_exact_order_six
#print axioms dirk_order_six_isLeast_charZero_field
