module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Five rational stages of exact strict SDIRK order five

An integer-scaled replay pays the reviewed order conditions. A single tall
condition at order six fails. This is only an upper construction.
-/

namespace RKResearch.Certified.RationalStrictSDIRKFiveStageFiveUpper

open FiniteRootedTree
open scoped Matrix

/-- The chronological stage numerator matrix `522112794934500 A`. -/
def AInt : Matrix (Fin 5) (Fin 5) ℤ :=
  !![522112794934500,0,0,0,0;
     -284788797237000,522112794934500,0,0,0;
     2683839804858135,-2370572127897435,522112794934500,0,0;
     -26599827494363277,15255628448496557,11657466722827420,522112794934500,0;
     981799060039875,-1398816686911875,-94694970562500,-10400197500000,522112794934500]

/-- The output numerator row `22771717920 b`. -/
def bInt : Fin 5 → ℤ := ![4954957140,14700208204,-197635000,40753125,3273434451]

def A : Matrix (Fin 5) (Fin 5) ℚ := Matrix.of fun i j => (AInt i j : ℚ) / 522112794934500

def b : Fin 5 → ℚ := fun i => (bInt i : ℚ) / 22771717920

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 5, i < j → A i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem common_diagonal : ∀ i, A i i = 1 := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked :
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 522112794934500 22771717920 5 = true := by
  decide +kernel

theorem order_five : HasOrder 5 A b := by
  refine hasOrder_of_scaled_check (A := AInt) (b := bInt) (d := 522112794934500) (e := 22771717920) (p := 5)
    (Int.castRingHom ℚ) (fun _ => rfl) (fun _ => rfl) ?_ ?_
    (isUnit_iff_ne_zero.mpr (by decide +kernel))
    (isUnit_iff_ne_zero.mpr (by decide +kernel)) checked
  · funext i j
    change (AInt i j : ℚ) = (522112794934500 : ℚ) * ((AInt i j : ℚ) / 522112794934500)
    exact (mul_div_cancel₀ (AInt i j : ℚ) (by decide +kernel : (522112794934500 : ℚ) ≠ 0)).symm
  · funext i
    change (bInt i : ℚ) = (22771717920 : ℚ) * ((bInt i : ℚ) / 22771717920)
    exact (mul_div_cancel₀ (bInt i : ℚ) (by decide +kernel : (22771717920 : ℚ) ≠ 0)).symm

set_option maxHeartbeats 4000000 in
/-- Only this next-order tall tree is used to make the witness exact. -/
theorem sixth_tall_weight : b ⬝ᵥ Φ (tallTree 6) A = (-5 / 24 : ℚ) := by
  decide +kernel

theorem not_order_six : ¬ HasOrder 6 A b := by
  intro h
  have paid := h (tallTree 6) (by rw [order_tallTree] <;> decide)
  rw [sixth_tall_weight] at paid
  exact (by decide +kernel : ((tallTree 6).factorial : ℚ) * (-5 / 24 : ℚ) ≠ 1) paid

end RKResearch.Certified.RationalStrictSDIRKFiveStageFiveUpper

namespace RKResearch.Certified

/-- Five rational stages suffice for exact order five at fixed diagonal one. -/
theorem exists_five_stage_rational_strictSDIRK_exact_five :
    ∃ (A : Matrix (Fin 5) (Fin 5) ℚ) (b : Fin 5 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
        HasOrder 5 A b ∧ ¬ HasOrder 6 A b :=
  ⟨RationalStrictSDIRKFiveStageFiveUpper.A, RationalStrictSDIRKFiveStageFiveUpper.b,
    RationalStrictSDIRKFiveStageFiveUpper.lowerTriangular,
    RationalStrictSDIRKFiveStageFiveUpper.common_diagonal, one_ne_zero,
    RationalStrictSDIRKFiveStageFiveUpper.order_five, RationalStrictSDIRKFiveStageFiveUpper.not_order_six⟩

end RKResearch.Certified
