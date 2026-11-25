module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallValues
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallSteps.Step02
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallSteps.Step03
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallSteps.Step04
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallSteps.Step05
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallSteps.Step06
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallSteps.Step07
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallSteps.Step08
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallSteps.Step09
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallSteps.Step10

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open scoped Matrix

private theorem tenth_tall_int : bInt ⬝ᵥ Φ (tallTree 10) AInt = tenthTallNumerator := by
  have h1 : Φ (tallTree 1) AInt = tallVec1 := rfl
  have h2 : Φ (tallTree 2) AInt = tallVec2 := by
    change (1 : Fin 23 → ℤ) * (AInt *ᵥ Φ (tallTree 1) AInt) = tallVec2
    simpa only [one_mul, h1] using tall_step2
  have h3 : Φ (tallTree 3) AInt = tallVec3 := by
    change (1 : Fin 23 → ℤ) * (AInt *ᵥ Φ (tallTree 2) AInt) = tallVec3
    simpa only [one_mul, h2] using tall_step3
  have h4 : Φ (tallTree 4) AInt = tallVec4 := by
    change (1 : Fin 23 → ℤ) * (AInt *ᵥ Φ (tallTree 3) AInt) = tallVec4
    simpa only [one_mul, h3] using tall_step4
  have h5 : Φ (tallTree 5) AInt = tallVec5 := by
    change (1 : Fin 23 → ℤ) * (AInt *ᵥ Φ (tallTree 4) AInt) = tallVec5
    simpa only [one_mul, h4] using tall_step5
  have h6 : Φ (tallTree 6) AInt = tallVec6 := by
    change (1 : Fin 23 → ℤ) * (AInt *ᵥ Φ (tallTree 5) AInt) = tallVec6
    simpa only [one_mul, h5] using tall_step6
  have h7 : Φ (tallTree 7) AInt = tallVec7 := by
    change (1 : Fin 23 → ℤ) * (AInt *ᵥ Φ (tallTree 6) AInt) = tallVec7
    simpa only [one_mul, h6] using tall_step7
  have h8 : Φ (tallTree 8) AInt = tallVec8 := by
    change (1 : Fin 23 → ℤ) * (AInt *ᵥ Φ (tallTree 7) AInt) = tallVec8
    simpa only [one_mul, h7] using tall_step8
  have h9 : Φ (tallTree 9) AInt = tallVec9 := by
    change (1 : Fin 23 → ℤ) * (AInt *ᵥ Φ (tallTree 8) AInt) = tallVec9
    simpa only [one_mul, h8] using tall_step9
  have h10 : Φ (tallTree 10) AInt = tallVec10 := by
    change (1 : Fin 23 → ℤ) * (AInt *ᵥ Φ (tallTree 9) AInt) = tallVec10
    simpa only [one_mul, h9] using tall_step10
  calc
    bInt ⬝ᵥ Φ (tallTree 10) AInt = outInt tallVec10 := by rw [h10, outInt_eq]
    _ = tenthTallNumerator := by decide +kernel

theorem tenth_tall_weight : b ⬝ᵥ Φ (tallTree 10) A = (672263002006281827534440264169 / 2489086143060781104997013158963200000 : ℚ) := by
  have h := congrArg (Int.castRingHom ℚ) tenth_tall_int
  simp only [RingHom.map_dotProduct, RKResearch.map_Φ, cast_AInt, cast_bInt,
    Φ_matrix_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, order_tallTree] at h
  have scaled :
      (stageScale : ℚ) ^ (9 : ℕ) * ((weightScale : ℚ) * (b ⬝ᵥ Φ (tallTree 10) A)) =
        (tenthTallNumerator : ℚ) := by
    first
    | exact h
    | simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have expected :
      (stageScale : ℚ) ^ (9 : ℕ) * ((weightScale : ℚ) * (672263002006281827534440264169 / 2489086143060781104997013158963200000 : ℚ)) =
        (tenthTallNumerator : ℚ) := by
    decide +kernel
  have unscale := mul_left_cancel₀ (by decide +kernel : (stageScale : ℚ) ^ (9 : ℕ) ≠ 0)
    (scaled.trans expected.symm)
  exact mul_left_cancel₀ weightScale_ne_zero unscale

theorem not_order_ten : ¬ HasOrder 10 A b := by
  intro h
  have paid := h (tallTree 10) (by rw [order_tallTree] <;> decide +kernel)
  rw [tenth_tall_weight] at paid
  exact (by decide +kernel : ((tallTree 10).factorial : ℚ) * (672263002006281827534440264169 / 2489086143060781104997013158963200000 : ℚ) ≠ 1) paid

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
