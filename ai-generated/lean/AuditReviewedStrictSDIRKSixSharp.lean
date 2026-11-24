import RKCert.ReviewedNative.SDIRKSixSharp

open RKResearch RKResearch.Certified

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

example :
    ∃ (A : Matrix (Fin 7) (Fin 7) ℝₐ) (b : Fin 7 → ℝₐ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/2) ∧ (1/2:ℝₐ) ≠ 0 ∧
        HasOrder 6 A b ∧ ¬ HasOrder 7 A b :=
  LaguerreGauss76.exact_realAlgebraic

example :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (γ : ℝ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 6 A b} 7 :=
  strictSDIRK_order_six_isLeast_real

#print axioms LaguerreGauss76.order_six
#print axioms LaguerreGauss76.not_order_seven
#print axioms LaguerreGauss76.exact_map
#print axioms LaguerreGauss76.exact_realAlgebraic
#print axioms LaguerreGauss76.exact_real
#print axioms strictSDIRK_order_six_isLeast_of_sq_roots
#print axioms strictSDIRK_order_six_isLeast_realAlgebraic
#print axioms strictSDIRK_order_six_isLeast_real
