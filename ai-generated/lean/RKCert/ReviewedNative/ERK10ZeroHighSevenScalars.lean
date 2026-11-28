import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10ZeroHighSevenScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

theorem homogeneousSecondEndpoint (a b A B : R)
    (r1 : a*A+b*B=0) (r2 : 2*a*b*A+3*b^2*B=0) :
    a*b*A=0 ∧ b^2*B=0 := by
  constructor
  · calc
      _ = 3*b*(a*A+b*B)-(2*a*b*A+3*b^2*B) := by clear r1 r2; grind
      _ = 0 := by rw [r1,r2]; grind
  · calc
      _ = (2*a*b*A+3*b^2*B)-2*b*(a*A+b*B) := by clear r1 r2; grind
      _ = 0 := by rw [r1,r2]; grind

/-- Numerator after clearing denominators of the exceptional
two-mode cubic payment. A nonzero ordinary target must equal
the two-copy invisible ordinate, which is not an ordinary site. -/
theorem invisibleThirdColumnResidual (a b z : R) :
    (-3*z^2+4*(a+b)*z-6*a*b)+(a-2*b)*(2*z-3*a) =
      -3*(z-a)^2 := by grind

theorem dormantRepeatCubicHead (p z : R) :
    5*p*(2*p)-3*p*z-4*(2*p)^2+3*(2*p)*z=3*p*(z-2*p) ∧
    -3*z^2+4*(p+2*p)*z-6*p*(2*p)=-3*(z-2*p)^2 := by grind

theorem threeEndpointGhostSquare (a t x S T w : R)
    (rel : 2*t=3*a)
    (h1 : 2*(a*S+t*T)=w*x^2)
    (h2 : 3*(a^2*S+t^2*T)=w*x^3)
    (h3 : 9*a^3*S+8*t^3*T=2*w*x^4) :
    2*w*x^2*(x-t)^2=0 := by
  calc
    _ = 2*t^2*(w*x^2)-4*t*(w*x^3)+2*w*x^4 := by clear rel h1 h2 h3; grind
    _ = 2*t^2*(2*(a*S+t*T))-4*t*(3*(a^2*S+t^2*T))+(9*a^3*S+8*t^3*T) := by
      rw [←h1, ←h2, ←h3]
    _ = a*(2*t-3*a)^2*S := by clear rel h1 h2 h3; grind
    _ = 0 := by rw [rel]; grind

end Ring
end RKResearch.Certified.ERK10ZeroHighSevenScalars
#print axioms RKResearch.Certified.ERK10ZeroHighSevenScalars.homogeneousSecondEndpoint
#print axioms RKResearch.Certified.ERK10ZeroHighSevenScalars.invisibleThirdColumnResidual
#print axioms RKResearch.Certified.ERK10ZeroHighSevenScalars.dormantRepeatCubicHead
#print axioms RKResearch.Certified.ERK10ZeroHighSevenScalars.threeEndpointGhostSquare
