module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Seven rational stages of exact strict SDIRK order six

An integer-scaled replay pays the reviewed order conditions. A single tall
condition at order seven fails. This is only an upper construction.
-/

namespace RKResearch.Certified.RationalStrictSDIRKSevenStageSixUpper

open FiniteRootedTree
open scoped Matrix

/-- The chronological stage numerator matrix `1536 A`. -/
def AInt : Matrix (Fin 7) (Fin 7) ℤ :=
  !![384,0,0,0,0,0,0;
     -768,384,0,0,0,0,0;
     -192,-192,384,0,0,0,0;
     1984,448,-1280,384,0,0,0;
     224,32,176,-48,384,0,0;
     238,106,-155,27,-216,384,0;
     -714,-174,621,-93,360,768,384]

/-- The output numerator row `90 b`. -/
def bInt : Fin 7 → ℤ := ![0,0,7,7,12,32,32]

def A : Matrix (Fin 7) (Fin 7) ℚ := Matrix.of fun i j => (AInt i j : ℚ) / 1536

def b : Fin 7 → ℚ := fun i => (bInt i : ℚ) / 90

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 7, i < j → A i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem common_diagonal : ∀ i, A i i = 1/4 := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked :
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 1536 90 6 = true := by
  decide +kernel

theorem order_six : HasOrder 6 A b := by
  refine hasOrder_of_scaled_check (A := AInt) (b := bInt) (d := 1536) (e := 90) (p := 6)
    (Int.castRingHom ℚ) (fun _ => rfl) (fun _ => rfl) ?_ ?_
    (isUnit_iff_ne_zero.mpr (by decide +kernel))
    (isUnit_iff_ne_zero.mpr (by decide +kernel)) checked
  · funext i j
    change (AInt i j : ℚ) = (1536 : ℚ) * ((AInt i j : ℚ) / 1536)
    exact (mul_div_cancel₀ (AInt i j : ℚ) (by decide +kernel : (1536 : ℚ) ≠ 0)).symm
  · funext i
    change (bInt i : ℚ) = (90 : ℚ) * ((bInt i : ℚ) / 90)
    exact (mul_div_cancel₀ (bInt i : ℚ) (by decide +kernel : (90 : ℚ) ≠ 0)).symm

set_option maxHeartbeats 4000000 in
/-- Only this next-order tall tree is used to make the witness exact. -/
theorem seventh_tall_weight : b ⬝ᵥ Φ (tallTree 7) A = (7 / 40960 : ℚ) := by
  decide +kernel

theorem not_order_seven : ¬ HasOrder 7 A b := by
  intro h
  have paid := h (tallTree 7) (by rw [order_tallTree] <;> decide)
  rw [seventh_tall_weight] at paid
  exact (by decide +kernel : ((tallTree 7).factorial : ℚ) * (7 / 40960 : ℚ) ≠ 1) paid

end RKResearch.Certified.RationalStrictSDIRKSevenStageSixUpper

namespace RKResearch.Certified

/-- Seven rational stages suffice for exact order six at fixed diagonal one quarter. -/
theorem exists_seven_stage_rational_strictSDIRK_exact_six :
    ∃ (A : Matrix (Fin 7) (Fin 7) ℚ) (b : Fin 7 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/4) ∧ (1/4 : ℚ) ≠ 0 ∧
        HasOrder 6 A b ∧ ¬ HasOrder 7 A b :=
  ⟨RationalStrictSDIRKSevenStageSixUpper.A, RationalStrictSDIRKSevenStageSixUpper.b,
    RationalStrictSDIRKSevenStageSixUpper.lowerTriangular,
    RationalStrictSDIRKSevenStageSixUpper.common_diagonal, by decide +kernel,
    RationalStrictSDIRKSevenStageSixUpper.order_six, RationalStrictSDIRKSevenStageSixUpper.not_order_seven⟩

end RKResearch.Certified
