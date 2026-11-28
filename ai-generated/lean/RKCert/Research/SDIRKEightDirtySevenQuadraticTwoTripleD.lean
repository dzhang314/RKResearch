import Mathlib.Tactic.Ring.Basic

/-! Scalar Vieta reductions for the quadratic two-triple-D chart. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoTripleD

variable {R : Type*} [CommRing R]

theorem shared_center_vieta (u : R) :
    (1+2*u-u^2)*(1-2*u-u^2)=u^4-6*u^2+1 := by
  ring1

theorem shared_center_remainder (u : R) :
    224*u^4-84*u^2=8*(28*u^4-21*u^2+3)+84*u^2-24 := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoTripleD
