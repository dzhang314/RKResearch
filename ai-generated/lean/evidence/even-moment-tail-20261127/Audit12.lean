import ProofEven12

open RKResearch

example : ∃ (A : Matrix (Fin 28) (Fin 28) ℚ) (b : Fin 28 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = (1:ℚ)/4) ∧ (1:ℚ)/4 ≠ 0 ∧
    HasOrder 12 A b ∧ ¬ HasOrder 13 A b :=
  RKResearch.Certified.EvenTerminal12.witness

#print axioms RKResearch.Certified.EvenTerminal12.witness
#print axioms RKResearch.Certified.EvenTerminal12.copies
#print axioms RKResearch.Certified.Seed10Even.donor_pure
