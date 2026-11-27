import Stage19

open RKResearch

example : ∃ (A : Matrix (Fin 72) (Fin 72) ℚ) (b : Fin 72 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
    HasOrder 19 A b ∧ ¬ HasOrder 20 A b :=
  RKResearch.Certified.FixedOneOrder19.witness

example (j : Fin 5) :
    RKResearch.Certified.TwoDonorDense.PureAt
      RKResearch.Certified.FixedOneOrder19.A
      (RKResearch.Certified.FixedOneOrder19.bankIndex j) 11 :=
  RKResearch.Certified.FixedOneOrder19.pure_bank j

#print axioms RKResearch.Certified.FixedOneOrder19.witness
#print axioms RKResearch.Certified.FixedOneOrder19.pure_bank
#print axioms RKResearch.Certified.FixedOneOrder19.virtual_copies
