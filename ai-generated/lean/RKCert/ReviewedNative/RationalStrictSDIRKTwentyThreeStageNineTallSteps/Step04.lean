module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallValues

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKSparseRows
open scoped Matrix

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem step4_check : checkFin (fun i : Fin 23 =>
    decide (actInt tallVec3 i = tallVec4 i)) = true := by
  decide +kernel

theorem tall_step4 : AInt *ᵥ tallVec3 = tallVec4 := by
  rw [← actInt_eq]
  funext i
  exact of_decide_eq_true (checkFin_get _ step4_check i)

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
