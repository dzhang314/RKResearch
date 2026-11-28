/-! Local endpoint chronology and exact scalar denial at the regular good place. -/
namespace RKResearch.ERK11EndpointAliasRegularGate
open Lean.Grind

theorem liveOuterClock {R : Type} [CommRing R] (C z H p v : R)
    (h : C-z*H = -p*z*v) (hc : C≠0) : z≠0 := by
  intro hz
  rw [hz] at h
  grind

theorem paidLeftPairObstruction :
    ((29-14*16)^2-(16-14*14)*(36-14*29) : Int) % 37 = 26 ∧ (26 : Int) % 37 ≠ 0 := by
  decide

end RKResearch.ERK11EndpointAliasRegularGate
#print axioms RKResearch.ERK11EndpointAliasRegularGate.liveOuterClock
#print axioms RKResearch.ERK11EndpointAliasRegularGate.paidLeftPairObstruction
