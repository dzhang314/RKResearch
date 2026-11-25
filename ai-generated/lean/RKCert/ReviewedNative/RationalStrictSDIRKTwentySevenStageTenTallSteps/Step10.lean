module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenData
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenTallValues

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper

open RationalStrictSDIRKSparseRows
open scoped Matrix

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem step10_check : checkFin (fun i : Fin 27 =>
    decide (actInt tallVec9 i = tallVec10 i)) = true := by
  decide +kernel

theorem tall_step10 : AInt *ᵥ tallVec9 = tallVec10 := by
  rw [← actInt_eq]
  funext i
  exact of_decide_eq_true (checkFin_get _ step10_check i)

end RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper
