module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# Three exact-order rational tableaux over the reviewed order conditions

The positive proofs use the complete finite checker on the reviewed tree
datatype. For each negative result, one reviewed bushy-tree moment suffices;
its exact rational value records the counterexample. Bounds are statements
about the displayed tableaux, not lower bounds on their method classes.
-/

namespace RKResearch.Certified
open FiniteRootedTree
open scoped Matrix

namespace ClassicalRK4

/-- The classical four-stage strictly lower triangular tableau. -/
def A : Matrix (Fin 4) (Fin 4) ℚ := Matrix.of fun i j =>
  match i.val, j.val with
  | 1, 0 => 1/2
  | 2, 1 => 1/2
  | 3, 2 => 1
  | _, _ => 0

/-- Endpoint weights `1/6`, interior weights `1/3`. -/
def b (i : Fin 4) : ℚ := if i.val = 0 ∨ i.val = 3 then 1/6 else 1/3

theorem explicit : ∀ i j : Fin 4, i ≤ j → A i j = 0 := by
  simp only [A, Matrix.of_apply]
  decide +kernel

theorem order_four : HasOrder A b 4 := by
  apply (checkOrder_iff A b 4).mp
  decide +kernel

theorem fifth_bush_value :
    (((bushyTree 5).factorial : ℕ) : ℚ) * (b ⬝ᵥ Φ (bushyTree 5) A) = 25/24 := by
  rw [factorial_bushyTree, Φ_bushyTree]
  decide +kernel

theorem not_order_five : ¬ HasOrder A b 5 := by
  intro h
  have ht := h (bushyTree 5) (by rw [order_bushyTree]; decide)
  rw [fifth_bush_value] at ht
  exact (by decide +kernel : (25/24 : ℚ) ≠ 1) ht

end ClassicalRK4

namespace ImplicitMidpoint

/-- One stage, with common nonzero diagonal `1/2`. -/
def A : Matrix (Fin 1) (Fin 1) ℚ := Matrix.of fun _ _ => 1/2

def b (_ : Fin 1) : ℚ := 1

theorem lowerTriangular : Matrix.IsLowerTriangular A := by
  change ∀ i j : Fin 1, i < j → A i j = 0
  simp only [A, Matrix.of_apply]
  decide +kernel

theorem common_diagonal (i : Fin 1) : A i i = 1/2 := rfl

theorem diagonal_ne_zero (i : Fin 1) : A i i ≠ 0 := by
  change (1/2 : ℚ) ≠ 0
  decide +kernel

theorem order_two : HasOrder A b 2 := by
  apply (checkOrder_iff A b 2).mp
  decide +kernel

theorem third_bush_value :
    (((bushyTree 3).factorial : ℕ) : ℚ) * (b ⬝ᵥ Φ (bushyTree 3) A) = 3/4 := by
  rw [factorial_bushyTree, Φ_bushyTree]
  decide +kernel

theorem not_order_three : ¬ HasOrder A b 3 := by
  intro h
  have ht := h (bushyTree 3) (by rw [order_bushyTree]; decide)
  rw [third_bush_value] at ht
  exact (by decide +kernel : (3/4 : ℚ) ≠ 1) ht

end ImplicitMidpoint

namespace MidpointExtrapolation4

/-- One full implicit-midpoint step and two half steps, extrapolated to order four. -/
def A : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun i j =>
  match i.val, j.val with
  | 0, 0 => 1/2
  | 1, 1 => 1/4
  | 2, 1 => 1/2
  | 2, 2 => 1/4
  | _, _ => 0

def b (i : Fin 3) : ℚ := if i.val = 0 then -1/3 else 2/3

theorem lowerTriangular : Matrix.IsLowerTriangular A := by
  change ∀ i j : Fin 3, i < j → A i j = 0
  simp only [A, Matrix.of_apply]
  decide +kernel

theorem not_common_diagonal : ¬ ∃ γ : ℚ, ∀ i, A i i = γ := by
  rintro ⟨γ, h⟩
  exact (by decide +kernel : A 0 0 ≠ A 1 1) ((h 0).trans (h 1).symm)

theorem order_four : HasOrder A b 4 := by
  apply (checkOrder_iff A b 4).mp
  decide +kernel

theorem fifth_bush_value :
    (((bushyTree 5).factorial : ℕ) : ℚ) * (b ⬝ᵥ Φ (bushyTree 5) A) = 185/192 := by
  rw [factorial_bushyTree, Φ_bushyTree]
  decide +kernel

theorem not_order_five : ¬ HasOrder A b 5 := by
  intro h
  have ht := h (bushyTree 5) (by rw [order_bushyTree]; decide)
  rw [fifth_bush_value] at ht
  exact (by decide +kernel : (185/192 : ℚ) ≠ 1) ht

end MidpointExtrapolation4

end RKResearch.Certified
