import Symbolic13

open RKResearch

example : ∃ (A : Matrix (Fin 35) (Fin 35) ℚ) (b : Fin 35 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
    HasOrder 13 A b ∧ ¬ HasOrder 14 A b :=
  RKResearch.Certified.FixedOneOrder13.witness

#print axioms RKResearch.Certified.FixedOneOrder13.witness
#print axioms RKResearch.Certified.FixedOneOrder13.virtual_copies
#print axioms RKResearch.Certified.Seed11Donors.pure20
