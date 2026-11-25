module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTallValues

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKSparseRows
open scoped Matrix

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem step9_check : checkFin (fun i : Fin 23 =>
    decide (actInt tallVec8 i = tallVec9 i)) = true := by
  decide +kernel

theorem tall_step9 : AInt *ᵥ tallVec8 = tallVec9 := by
  rw [← actInt_eq]
  funext i
  exact of_decide_eq_true (checkFin_get _ step9_check i)

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
