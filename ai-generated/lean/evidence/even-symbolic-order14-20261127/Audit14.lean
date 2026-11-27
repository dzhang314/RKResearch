import ProofEven14

open RKResearch
open RKResearch.Certified
open RKResearch.Certified.TwoDonorDense
set_option autoImplicit false

example : ∃ (A : Matrix (Fin 38) (Fin 38) ℚ) (b : Fin 38 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = (1:ℚ)/4) ∧ (1:ℚ)/4 ≠ 0 ∧
    HasOrder 14 A b ∧ ¬ HasOrder 15 A b :=
  EvenTerminal14.witness

example : HasOrder 12 EvenPrep12.A EvenPrep12.b := EvenPrep12.order

example (i : Fin 6) : PureAt EvenPrep12.A (EvenPrep12.headIndex i) 7 :=
  EvenPrep12.pure_head i

example (i : Fin 3) : PureAt EvenPrep12.A (EvenPrep12.highIndex i) 8 :=
  EvenPrep12.pure_high i

#print axioms EvenTerminal14.witness
#print axioms EvenTerminal14.copies
#print axioms EvenPrep12.order
#print axioms EvenPrep12.pure_head
#print axioms EvenPrep12.pure_high
