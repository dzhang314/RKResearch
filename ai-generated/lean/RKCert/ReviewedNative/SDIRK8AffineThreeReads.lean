module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8AffineThreeReads

/-- The active literal and fourth, together with a genuinely weighted
virtual reading at a distinct silent clock, must be compatible with
one affine denominator. The statement does not identify that reading
with an individual silent defect. -/
theorem affineThreeReads {R : Type*} [CommRing R]
    (a b s q₀ q₁ Qa Qb Qs : R)
    (ha : Qa=q₀+q₁*a) (hb : Qb=q₀+q₁*b) (hs : Qs=q₀+q₁*s) :
    (s-b)*Qa+(b-a)*Qs+(a-s)*Qb=0 := by
  linear_combination (s-b)*ha+(b-a)*hs+(a-s)*hb

#print axioms affineThreeReads

end RKCert.ReviewedNative.SDIRK8AffineThreeReads
