import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10TripleEndpointInteriorPairScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

theorem trackingFactors (s t : R) (p : 4*s+15*t=0) (q : 5*s+21*t=0) :
    9*s=0 ∧ 9*t=0 := by
  constructor
  · calc
      _=21*(4*s+15*t)-15*(5*s+21*t) := by clear p q; grind
      _=0 := by rw [p,q]; grind
  · calc
      _=4*(5*s+21*t)-5*(4*s+15*t) := by clear p q; grind
      _=0 := by rw [p,q]; grind

theorem correctedCubicSquare (a t x w S T : R) (clock : 2*t=3*a)
    (p2 : 2*(a*S+t*T)=w*x^2)
    (p3 : 3*(a^2*S+t^2*T)=w*x^3)
    (p4 : 9*a^3*S+8*t^3*T=2*w*x^4) :
    2*w*x^2*(x-t)^2=0 := by
  calc
    _=2*t^2*(w*x^2)-4*t*(w*x^3)+2*w*x^4 := by clear clock p2 p3 p4; grind
    _=a*(2*t-3*a)^2*S := by rw [←p2,←p3,←p4]; grind
    _=0 := by rw [clock]; grind
end Ring

section Field
variable {F : Type} [Field F]

theorem trackingExit (s t : F) (nine : (9:F) ≠ 0)
    (p : 4*s+15*t=0) (q : 5*s+21*t=0) : s=0 ∧ t=0 := by
  obtain ⟨hs,ht⟩ := trackingFactors s t p q
  clear p q
  exact ⟨by grind, by grind⟩

theorem correctedExit (a t x w S T : F) (clock : 2*t=3*a)
    (two : (2:F) ≠ 0) (wn : w ≠ 0) (xn : x ≠ 0)
    (p2 : 2*(a*S+t*T)=w*x^2)
    (p3 : 3*(a^2*S+t^2*T)=w*x^3)
    (p4 : 9*a^3*S+8*t^3*T=2*w*x^4) : x=t := by
  have h := correctedCubicSquare a t x w S T clock p2 p3 p4
  clear clock p2 p3 p4 S T a
  grind

end Field
end RKResearch.Certified.ERK10TripleEndpointInteriorPairScalars
#print axioms RKResearch.Certified.ERK10TripleEndpointInteriorPairScalars.trackingExit
#print axioms RKResearch.Certified.ERK10TripleEndpointInteriorPairScalars.correctedExit
