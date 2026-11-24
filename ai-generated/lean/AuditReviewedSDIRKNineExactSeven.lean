import RKCert.ReviewedNative.SDIRKNineExactSeven

open RKResearch RKResearch.Certified.SDIRKNineReplay

example :
    ∃ (A : Matrix (Fin 9) (Fin 9) ℝ) (b : Fin 9 → ℝ) (γ : ℝ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧
        HasOrder A b 7 ∧ ¬ HasOrder A b 8 :=
  exists_exact_real

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

example :
    ∃ (A : Matrix (Fin 9) (Fin 9) ℝₐ) (b : Fin 9 → ℝₐ) (γ : ℝₐ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧
        HasOrder A b 7 ∧ ¬ HasOrder A b 8 :=
  exists_exact_realAlgebraic

#print axioms not_order_eight_real
#print axioms exists_exact_real
#print axioms exists_exact_realAlgebraic
