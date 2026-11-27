import Stage17

open RKResearch

example : ∃ (A : Matrix (Fin 58) (Fin 58) ℚ) (b : Fin 58 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
    HasOrder 17 A b ∧ ¬ HasOrder 18 A b :=
  RKResearch.Certified.FixedOneOrder17.witness

example (j : Fin 4) :
    RKResearch.Certified.TwoDonorDense.PureAt
      RKResearch.Certified.FixedOneOrder17.A
      (RKResearch.Certified.FixedOneOrder17.bankIndex j) 10 :=
  RKResearch.Certified.FixedOneOrder17.pure_bank j

#print axioms RKResearch.Certified.FixedOneOrder17.witness
#print axioms RKResearch.Certified.FixedOneOrder17.pure_bank
#print axioms RKResearch.Certified.FixedOneOrder17.virtual_copies
