module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Field.Rat

@[expose] public section

/-!
# An exact seven-stage, order-seven rational DIRK tableau

This is the zero-central-parameter tableau on the nodes `(0,3,4,8,10,13,14)/14`
from the rational endpoint-Christoffel seed. No family theorem or optimality is
assumed: the matrix and output row below are the entire input to this proof.
-/

namespace RKResearch.Certified.RationalDIRK7

open FiniteRootedTree
open scoped Matrix

/-- The lower-triangular coefficient matrix, stages numbered from zero. -/
def A : Matrix (Fin 7) (Fin 7) ℚ := Matrix.of fun i j =>
  match i.val, j.val with
  | 1, 0 => 3/28
  | 1, 1 => 3/28
  | 2, 0 => 359/441
  | 2, 1 => -1184/441
  | 2, 2 => 317/147
  | 3, 0 => 166/441
  | 3, 1 => -664/441
  | 3, 2 => 250/147
  | 4, 0 => -2261/936
  | 4, 1 => 4574/315
  | 4, 2 => -3481/273
  | 4, 3 => 673/520
  | 4, 4 => 6/91
  | 5, 0 => 51833/38808
  | 5, 1 => -65189/9702
  | 5, 2 => 159925/25872
  | 5, 3 => -3/112
  | 5, 4 => 75/616
  | 5, 5 => 1/28
  | 6, 0 => 8543/872
  | 6, 1 => -87254/1635
  | 6, 2 => 138358/2943
  | 6, 3 => -31801/13080
  | 6, 4 => 440/981
  | 6, 5 => -6776/14715
  | _, _ => 0

/-- Output weights in chronological order. -/
def b (i : Fin 7) : ℚ :=
  match i.val with
  | 0 => 1/16
  | 1 => 476/1375
  | 2 => -49/2025
  | 3 => 2009/6000
  | 4 => 91/1080
  | 5 => 2156/10125
  | _ => -109/6600

/-- Every entry strictly above the diagonal vanishes (this is not an explicit RK matrix). -/
theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 7, i < j → A i j = 0
  simp only [A, Matrix.of_apply]
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- Independent positive certificate for *all* rooted trees through order seven. -/
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

/-- The seven abscissae, written independently of the matrix. -/
def c (i : Fin 7) : ℚ :=
  match i.val with
  | 0 => 0
  | 1 => 3 / 14
  | 2 => 2 / 7
  | 3 => 4 / 7
  | 4 => 5 / 7
  | 5 => 13 / 14
  | _ => 1

theorem row_sums : A *ᵥ 1 = c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 7, (A *ᵥ 1) i = c i) i

theorem variable_diagonal : A 1 1 ≠ 0 ∧ A 1 1 ≠ A 2 2 := by decide +kernel

/-- The reviewed order-eight bush asks for weight `1/8`; this tableau misses it. -/
theorem eighth_bush_weight : b ⬝ᵥ Φ (bushyTree 8) A = 167931/1344560 := by
  rw [Φ_bushyTree, row_sums]
  decide +kernel

theorem not_order_eight : ¬ HasOrder 8 A b := by
  intro h
  have ht := h (bushyTree 8) (by rw [order_bushyTree]; decide)
  rw [factorial_bushyTree, eighth_bush_weight] at ht
  exact (by decide +kernel : ¬ ((8 : ℚ) * (167931/1344560) = 1)) ht

end RKResearch.Certified.RationalDIRK7
