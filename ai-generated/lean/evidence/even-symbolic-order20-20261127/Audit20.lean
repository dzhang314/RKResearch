import ProofEven20

open RKResearch
open RKResearch.Certified
open RKResearch.Certified.TwoDonorDense
set_option autoImplicit false

example : ∃ (A : Matrix (Fin 75) (Fin 75) ℚ) (b : Fin 75 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = (1:ℚ)/4) ∧ (1:ℚ)/4 ≠ 0 ∧
    HasOrder 20 A b ∧ ¬ HasOrder 21 A b :=
  EvenTerminal20.witness

example : HasOrder 18 EvenPrep18.A EvenPrep18.b := EvenPrep18.order

example (i : Fin 9) : PureAt EvenPrep18.A (EvenPrep18.headIndex i) 10 :=
  EvenPrep18.pure_head i

example (i : Fin 5) : PureAt EvenPrep18.A (EvenPrep18.highIndex i) 11 :=
  EvenPrep18.pure_high i

#print axioms EvenTerminal20.witness
#print axioms EvenTerminal20.copies
#print axioms EvenPrep18.order
#print axioms EvenPrep18.pure_head
#print axioms EvenPrep18.pure_high
