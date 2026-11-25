module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenData
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenTallValues

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper

open RationalStrictSDIRKSparseRows
open scoped Matrix

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem step6_check : checkFin (fun i : Fin 27 =>
    decide (actInt tallVec5 i = tallVec6 i)) = true := by
  decide +kernel

theorem tall_step6 : AInt *ᵥ tallVec5 = tallVec6 := by
  rw [← actInt_eq]
  funext i
  exact of_decide_eq_true (checkFin_get _ step6_check i)

end RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper
