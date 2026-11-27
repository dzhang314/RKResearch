import ProofEven18

open RKResearch
open RKResearch.Certified
open RKResearch.Certified.TwoDonorDense
set_option autoImplicit false

example : ∃ (A : Matrix (Fin 61) (Fin 61) ℚ) (b : Fin 61 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = (1:ℚ)/4) ∧ (1:ℚ)/4 ≠ 0 ∧
    HasOrder 18 A b ∧ ¬ HasOrder 19 A b :=
  EvenTerminal18.witness

example : HasOrder 16 EvenPrep16.A EvenPrep16.b := EvenPrep16.order

example (i : Fin 8) : PureAt EvenPrep16.A (EvenPrep16.headIndex i) 9 :=
  EvenPrep16.pure_head i

example (i : Fin 4) : PureAt EvenPrep16.A (EvenPrep16.highIndex i) 10 :=
  EvenPrep16.pure_high i

#print axioms EvenTerminal18.witness
#print axioms EvenTerminal18.copies
#print axioms EvenPrep16.order
#print axioms EvenPrep16.pure_head
#print axioms EvenPrep16.pure_high
