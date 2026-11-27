import Lean

/-!
# Weighted order-nine moment certificate

For the weight (1-x)^2/2 on [0,1], the moments are
1 / ((k+1)(k+2)(k+3)). This file certifies the fixed 5-by-5
Gram factorization used in the weighted ERK order-nine support argument.
It does not assert the support inequality or a new RK stage bound.
-/

namespace RKResearch.WeightedOrderNineGram

def moment (k : Nat) : Rat :=
  1 / (((k+1)*(k+2)*(k+3) : Nat) : Rat)

def gram (i j : Fin 5) : Rat := moment (i.val + j.val)

def lower : Fin 5 → Fin 5 → Rat := fun i j =>
  (#[#[1, 0, 0, 0, 0],
     #[1/4, 1, 0, 0, 0],
     #[1/10, 2/3, 1, 0, 0],
     #[1/20, 3/7, 9/8, 1, 0],
     #[1/35, 2/7, 1, 8/5, 1]] : Array (Array Rat))[i.val]![j.val]!

def diagonal : Fin 5 → Rat := fun i =>
  (#[1/6, 1/160, 1/3150, 1/56448, 1/970200] : Array Rat)[i.val]!

def sum5 (f : Fin 5 → Rat) : Rat := f 0 + f 1 + f 2 + f 3 + f 4

theorem factorization : ∀ i j : Fin 5,
    gram i j = sum5 (fun k => lower i k * diagonal k * lower j k) := by
  decide +kernel

theorem diagonal_positive : ∀ i : Fin 5, 0 < diagonal i := by
  decide +kernel

theorem lower_unit_diagonal : ∀ i : Fin 5, lower i i = 1 := by
  decide +kernel

theorem lower_strict_upper_zero : ∀ i j : Fin 5,
    i < j → lower i j = 0 := by
  decide +kernel

end RKResearch.WeightedOrderNineGram

#print axioms RKResearch.WeightedOrderNineGram.factorization
#print axioms RKResearch.WeightedOrderNineGram.diagonal_positive
