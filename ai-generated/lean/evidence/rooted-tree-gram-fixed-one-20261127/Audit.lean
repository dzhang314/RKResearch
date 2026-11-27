import Certificate9
import Certificate11

open RKResearch

example : ∃ (A : Matrix (Fin 18) (Fin 18) ℚ) (b : Fin 18 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
    HasOrder 9 A b ∧ ¬ HasOrder 10 A b :=
  RKResearch.Certified.StrictSDIRKGram18Order9.witness

example : ∃ (A : Matrix (Fin 26) (Fin 26) ℚ) (b : Fin 26 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
    HasOrder 11 A b ∧ ¬ HasOrder 12 A b :=
  RKResearch.Certified.StrictSDIRKGram26Order11.witness

#print axioms RKResearch.Certified.StrictSDIRKGram18Order9.witness
#print axioms RKResearch.Certified.StrictSDIRKGram26Order11.witness
