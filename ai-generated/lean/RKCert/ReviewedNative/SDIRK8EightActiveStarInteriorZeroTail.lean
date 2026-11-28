module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveStarInteriorZeroTail

/-- Any three coefficient rows of the six-peg moment matrix must have zero
determinant: the missing monic quadratic supplies the kernel vector
`(u, v, 1)`. Neither the rows nor any pivot need to be nonzero. -/
theorem missingQuadraticMinor {R : Type*} [CommRing R]
    (a b c d e f g h i u v : R)
    (ha : a*u+b*v+c=0) (hb : d*u+e*v+f=0)
    (hc : g*u+h*v+i=0) :
    a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)=0 := by
  linear_combination (d*h-e*g)*ha+(b*g-a*h)*hb+(a*e-b*d)*hc

/-- The unknown common sign of the two actual rear clocks is immaterial
for the peg polynomial. This identity uses no division or square root. -/
theorem unorderedStarPair {R : Type*} [CommRing R] (X m γ v : R) :
    (X-(m-γ*v))*(X-(m+γ*v))=(X-m)^2-γ^2*v^2 := by ring

#print axioms missingQuadraticMinor
#print axioms unorderedStarPair

end RKCert.ReviewedNative.SDIRK8EightActiveStarInteriorZeroTail
