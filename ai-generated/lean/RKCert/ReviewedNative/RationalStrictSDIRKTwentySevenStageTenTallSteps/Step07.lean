module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenData
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenTallValues

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper

open RationalStrictSDIRKSparseRows
open scoped Matrix

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem step7_check : checkFin (fun i : Fin 27 =>
    decide (actInt tallVec6 i = tallVec7 i)) = true := by
  decide +kernel

theorem tall_step7 : AInt *ᵥ tallVec6 = tallVec7 := by
  rw [← actInt_eq]
  funext i
  exact of_decide_eq_true (checkFin_get _ step7_check i)

end RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper
