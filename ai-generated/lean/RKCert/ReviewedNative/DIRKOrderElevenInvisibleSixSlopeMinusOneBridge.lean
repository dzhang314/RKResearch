import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixSlopeMinusOneBridge

variable {K : Type*} [CommRing K]

def rhoNumerator (r s z y : K) : K :=
  (-9*r^2+48*s)*y^2+(8*r^2*z+3*r*s-42*s*z)*y-2*r*s*z

def oldHull (r s z y : K) : K :=
  15*y^3+(16*r-12*z)*y^2+(18*s-12*z*r)*y-12*z*s

theorem cleared_rho_identity (r s z y : K) :
    (2*r^2-9*s)*(10*s*y^2+5*r*y^3+3*y^4)
      -6*(y^2+r*y+s)*rhoNumerator r s z y
      = oldHull r s z y*((4*r^2-21*s)*y-r*s) := by
  unfold rhoNumerator oldHull
  ring

theorem rho_at_early_clock (r s z : K) :
    rhoNumerator r s z z = -z*((r^2-6*s)*z-r*s) := by
  unfold rhoNumerator
  ring

theorem ratio_from_mark {r s z c1 c2 : K}
    (h1 : 5*c1=6*s-4*z*r) (h2 : 15*c2=16*r-12*z) :
    5*(r*(c1+6*s)-6*c2*s)=4*(r*s-z*(r^2-6*s)) := by
  linear_combination r*h1-2*s*h2

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixSlopeMinusOneBridge
