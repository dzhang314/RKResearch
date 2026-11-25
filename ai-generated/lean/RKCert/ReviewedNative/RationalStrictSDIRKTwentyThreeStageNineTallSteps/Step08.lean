module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallValues

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKSparseRows
open scoped Matrix

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem step8_check : checkFin (fun i : Fin 23 =>
    decide (actInt tallVec7 i = tallVec8 i)) = true := by
  decide +kernel

theorem tall_step8 : AInt *ᵥ tallVec7 = tallVec8 := by
  rw [← actInt_eq]
  funext i
  exact of_decide_eq_true (checkFin_get _ step8_check i)

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
