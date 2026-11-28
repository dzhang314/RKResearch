module

public import RKCert.ReviewedNative.DIRK12Q36RealMomentDataBridge
import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.DIRK12Q36Moments

open IntegerPolyRootReplay IntegerPolyRootReplay.Packing

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem checked_head (j : Fin 5) :
    Packing.read (base:Int) (M0 j)=0 ∧ bound (M0 j)<base := by
  fin_cases j <;> decide +kernel

theorem checked_slope (j : Fin 5) :
    Packing.read (base:Int) (M1 j)=0 ∧ bound (M1 j)<base := by
  fin_cases j <;> decide +kernel

theorem momentChecks : MomentChecks := ⟨checked_head,checked_slope⟩

end RKResearch.Certified.DIRK12Q36Moments

#print axioms RKResearch.Certified.DIRK12Q36Moments.momentChecks
