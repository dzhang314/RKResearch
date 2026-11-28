module

public import RKCert.ReviewedNative.DIRKOrderTwelveMidpointGhostForwardCore

@[expose] public section

/-! The sixth ghost-tap moment is unpaid and deliberately retained. -/
namespace RKResearch.Certified.DIRK12MidpointGhost

def excess : Rat := 5/11088

def momentSix (k : Fin 6) : Rat :=
  1/((k.val+2:Nat):Rat) + if k.val=5 then excess else 0

theorem tap_moments_through_six :
    ∀ k : Fin 6, add4 (fun g => tap g*clock g^(k.val+1)) = momentSix k := by
  decide +kernel

theorem cubic_third_lift_tap : add4 (fun g => tap g*lift 3 g) = -1/47520 := by
  decide +kernel

end RKResearch.Certified.DIRK12MidpointGhost

#print axioms RKResearch.Certified.DIRK12MidpointGhost.tap_moments_through_six
#print axioms RKResearch.Certified.DIRK12MidpointGhost.cubic_third_lift_tap
