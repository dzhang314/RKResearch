module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Six rational stages of exact strict SDIRK order five

An integer-scaled replay pays the reviewed order conditions. A single tall
condition at order six fails. This is only an upper construction.
-/

namespace RKResearch.Certified.RationalStrictSDIRKSixStageFiveUpper

open FiniteRootedTree
open scoped Matrix

/-- The chronological stage numerator matrix `15750 A`. -/
def AInt : Matrix (Fin 6) (Fin 6) ℤ :=
  !![15750,0,0,0,0,0;
     -15750,15750,0,0,0,0;
     -7875,7875,15750,0,0,0;
     -7000,1750,0,15750,0,0;
     74781,-1827,-61740,-23814,15750,0;
     -567000,-23625,511875,91125,-28125,15750]

/-- The output numerator row `336 b`. -/
def bInt : Fin 6 → ℤ := ![0,0,35,162,125,14]

def A : Matrix (Fin 6) (Fin 6) ℚ := Matrix.of fun i j => (AInt i j : ℚ) / 15750

def b : Fin 6 → ℚ := fun i => (bInt i : ℚ) / 336

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 6, i < j → A i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem common_diagonal : ∀ i, A i i = 1 := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked :
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 15750 336 5 = true := by
  decide +kernel

theorem order_five : HasOrder 5 A b := by
  refine hasOrder_of_scaled_check (A := AInt) (b := bInt) (d := 15750) (e := 336) (p := 5)
    (Int.castRingHom ℚ) (fun _ => rfl) (fun _ => rfl) ?_ ?_
    (isUnit_iff_ne_zero.mpr (by decide +kernel))
    (isUnit_iff_ne_zero.mpr (by decide +kernel)) checked
  · funext i j
    change (AInt i j : ℚ) = (15750 : ℚ) * ((AInt i j : ℚ) / 15750)
    exact (mul_div_cancel₀ (AInt i j : ℚ) (by decide +kernel : (15750 : ℚ) ≠ 0)).symm
  · funext i
    change (bInt i : ℚ) = (336 : ℚ) * ((bInt i : ℚ) / 336)
    exact (mul_div_cancel₀ (bInt i : ℚ) (by decide +kernel : (336 : ℚ) ≠ 0)).symm

set_option maxHeartbeats 4000000 in
/-- Only this next-order tall tree is used to make the witness exact. -/
theorem sixth_tall_weight : b ⬝ᵥ Φ (tallTree 6) A = (-5 / 24 : ℚ) := by
  decide +kernel

theorem not_order_six : ¬ HasOrder 6 A b := by
  intro h
  have paid := h (tallTree 6) (by rw [order_tallTree] <;> decide)
  rw [sixth_tall_weight] at paid
  exact (by decide +kernel : ((tallTree 6).factorial : ℚ) * (-5 / 24 : ℚ) ≠ 1) paid

end RKResearch.Certified.RationalStrictSDIRKSixStageFiveUpper

namespace RKResearch.Certified

/-- Six rational stages suffice for exact order five at fixed diagonal one. -/
theorem exists_six_stage_rational_strictSDIRK_exact_five :
    ∃ (A : Matrix (Fin 6) (Fin 6) ℚ) (b : Fin 6 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
        HasOrder 5 A b ∧ ¬ HasOrder 6 A b :=
  ⟨RationalStrictSDIRKSixStageFiveUpper.A, RationalStrictSDIRKSixStageFiveUpper.b,
    RationalStrictSDIRKSixStageFiveUpper.lowerTriangular,
    RationalStrictSDIRKSixStageFiveUpper.common_diagonal, one_ne_zero,
    RationalStrictSDIRKSixStageFiveUpper.order_five, RationalStrictSDIRKSixStageFiveUpper.not_order_six⟩

end RKResearch.Certified
