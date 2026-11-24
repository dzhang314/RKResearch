import RKCert.ReviewedNative.LobattoDIRK109

open RKResearch RKResearch.Certified

example :
    ∃ (U : Matrix (Fin 10) (Fin 10) ℝ) (w : Fin 10 → ℝ),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder 9 U w :=
  LobattoDIRK109.exists_order_real

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

example :
    ∃ (U : Matrix (Fin 10) (Fin 10) ℝₐ) (w : Fin 10 → ℝₐ),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder 9 U w :=
  LobattoDIRK109.exists_order_realAlgebraic

example :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
      A.IsLowerTriangular ∧ HasOrder 9 A b} 10 :=
  dirk_order_nine_isLeast_real

example :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) ℝₐ) (b : Fin n → ℝₐ),
      A.IsLowerTriangular ∧ HasOrder 9 A b} 10 :=
  dirk_order_nine_isLeast_realAlgebraic

#print axioms LobattoDIRK109.act_val
#print axioms LobattoDIRK109.joins_correct
#print axioms LobattoDIRK109.deriv_correct
#print axioms LobattoDIRK109.moments
#print axioms LobattoDIRK109.exists_realAlgebraic_parameters
#print axioms LobattoDIRK109.order_nine
#print axioms dirk_order_nine_isLeast_of_roots
#print axioms dirk_order_nine_isLeast_real
#print axioms dirk_order_nine_isLeast_realAlgebraic
