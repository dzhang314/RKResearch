import Mathlib.Tactic.Ring

namespace RKResearch.Certified.ERK10FiveOpeningTwoPairScalars

variable {R : Type*} [CommRing R]

def F (a b y : R) : R := -3*y^2 + 4*(a+b)*y - 6*a*b
def Q (a y : R) : R := 2*y - 3*a

def H (a b t y : R) : R := t*F a b y + 12*(y-t)*(t-a)*(t-b)
def D (a t y : R) : R := t*Q a y - 6*(t-a)*(y-t)

theorem no_helper_determinant (a b z : R) :
    F a b a*Q a z-F a b z*Q a a = -3*a*(z-a)^2 := by
  simp only [F,Q]
  ring

theorem first_helper_determinant (a b t z : R) :
    H a b t z*D a t t-H a b t t*D a t z = -3*t^2*(z-t)^2*(2*t-3*a) := by
  simp only [F,Q,H,D]
  ring

end RKResearch.Certified.ERK10FiveOpeningTwoPairScalars

#print axioms RKResearch.Certified.ERK10FiveOpeningTwoPairScalars.no_helper_determinant
#print axioms RKResearch.Certified.ERK10FiveOpeningTwoPairScalars.first_helper_determinant
