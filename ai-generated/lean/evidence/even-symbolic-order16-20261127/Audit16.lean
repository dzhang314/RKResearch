import ProofEven16

open RKResearch
open RKResearch.Certified
open RKResearch.Certified.TwoDonorDense
set_option autoImplicit false

example : ∃ (A : Matrix (Fin 49) (Fin 49) ℚ) (b : Fin 49 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = (1:ℚ)/4) ∧ (1:ℚ)/4 ≠ 0 ∧
    HasOrder 16 A b ∧ ¬ HasOrder 17 A b :=
  EvenTerminal16.witness

example : HasOrder 14 EvenPrep14.A EvenPrep14.b := EvenPrep14.order

example (i : Fin 7) : PureAt EvenPrep14.A (EvenPrep14.headIndex i) 8 :=
  EvenPrep14.pure_head i

example (i : Fin 4) : PureAt EvenPrep14.A (EvenPrep14.highIndex i) 9 :=
  EvenPrep14.pure_high i

#print axioms EvenTerminal16.witness
#print axioms EvenTerminal16.copies
#print axioms EvenPrep14.order
#print axioms EvenPrep14.pure_head
#print axioms EvenPrep14.pure_high
