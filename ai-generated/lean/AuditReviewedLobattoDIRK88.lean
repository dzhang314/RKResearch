import RKCert.ReviewedNative.LobattoDIRK88

open RKResearch RKResearch.Certified

example :
    ∃ (U : Matrix (Fin 8) (Fin 8) ℝ) (w : Fin 8 → ℝ),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder U w 8 ∧ ¬ HasOrder U w 9 :=
  LobattoDIRK88.exists_exact_real

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

example :
    ∃ (U : Matrix (Fin 8) (Fin 8) ℝₐ) (w : Fin 8 → ℝₐ),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder U w 8 ∧ ¬ HasOrder U w 9 :=
  LobattoDIRK88.exists_exact_realAlgebraic

example :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
      A.IsLowerTriangular ∧ HasOrder A b 8} 8 :=
  dirk_order_eight_isLeast_real

example :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) ℝₐ) (b : Fin n → ℝₐ),
      A.IsLowerTriangular ∧ HasOrder A b 8} 8 :=
  dirk_order_eight_isLeast_realAlgebraic

#print axioms CanonicalStageMemo.cover
#print axioms LobattoDIRK88.act_val
#print axioms LobattoDIRK88.deriv_correct
#print axioms LobattoDIRK88.moments
#print axioms LobattoDIRK88.order_eight
#print axioms LobattoDIRK88.ninth_bush_scaled
#print axioms LobattoDIRK88.not_order_nine
#print axioms dirk_order_eight_isLeast_of_root
#print axioms dirk_order_eight_isLeast_real
#print axioms dirk_order_eight_isLeast_realAlgebraic
