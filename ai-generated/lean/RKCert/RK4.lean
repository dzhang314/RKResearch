module

public import RKCert.Enumeration
public import RKCert.StageBound
public import Mathlib.Algebra.Field.Rat

@[expose] public section

/-!
# Exact tree order of the classical four-stage Runge–Kutta tableau

All weights are rational. `by decide +kernel` below asks the kernel to check a closed
finite computation; the equivalence and stage bound are general theorems.
-/

namespace RKCert.ClassicalRK4

/-- The only nonzero entries are `A₂₁ = A₃₂ = 1/2` and `A₄₃ = 1` (one-based). -/
def A (i j : Fin 4) : ℚ :=
  match i.val, j.val with
  | 1, 0 => 1 / 2
  | 2, 1 => 1 / 2
  | 3, 2 => 1
  | _, _ => 0

/-- `(1/6, 1/3, 1/3, 1/6)`. -/
def b (i : Fin 4) : ℚ := if i.val = 0 ∨ i.val = 3 then 1 / 6 else 1 / 3

theorem explicit : StrictLower A := by
  unfold StrictLower
  decide +kernel

/-- Every rooted-tree identity through four vertices, including the branched trees. -/
theorem order_four : HasTreeOrderAtLeast A b 4 := by
  apply (checkTreeOrder_iff A b 4).mp
  decide +kernel

/-- The bound and the positive certificate meet: this tableau has *exactly* order four. -/
theorem not_order_five : ¬ HasTreeOrderAtLeast A b 5 := by
  intro h
  have hle := explicit_order_le_stages explicit h
  omega

end RKCert.ClassicalRK4
