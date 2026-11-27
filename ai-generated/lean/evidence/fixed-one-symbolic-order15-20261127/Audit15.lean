import Stage15

open RKResearch

example : ∃ (A : Matrix (Fin 46) (Fin 46) ℚ) (b : Fin 46 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
    HasOrder 15 A b ∧ ¬ HasOrder 16 A b :=
  RKResearch.Certified.FixedOneOrder15.witness

example (j : Fin 4) :
    RKResearch.Certified.TwoDonorDense.PureAt
      RKResearch.Certified.FixedOneOrder15.A
      (RKResearch.Certified.FixedOneOrder15.bankIndex j) 9 :=
  RKResearch.Certified.FixedOneOrder15.pure_bank j

#print axioms RKResearch.Certified.FixedOneOrder15.witness
#print axioms RKResearch.Certified.FixedOneOrder15.pure_bank
#print axioms RKResearch.Certified.FixedOneOrder15.virtual_copies
