module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenData
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenTallValues

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper

open RationalStrictSDIRKSparseRows
open scoped Matrix

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem step3_check : checkFin (fun i : Fin 27 =>
    decide (actInt tallVec2 i = tallVec3 i)) = true := by
  decide +kernel

theorem tall_step3 : AInt *ᵥ tallVec2 = tallVec3 := by
  rw [← actInt_eq]
  funext i
  exact of_decide_eq_true (checkFin_get _ step3_check i)

end RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper
