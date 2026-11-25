module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenData
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenTallValues

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper

open RationalStrictSDIRKSparseRows
open scoped Matrix

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem step2_check : checkFin (fun i : Fin 27 =>
    decide (actInt tallVec1 i = tallVec2 i)) = true := by
  decide +kernel

theorem tall_step2 : AInt *ᵥ tallVec1 = tallVec2 := by
  rw [← actInt_eq]
  funext i
  exact of_decide_eq_true (checkFin_get _ step2_check i)

end RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper
