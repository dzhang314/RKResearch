module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8GaussDoubleFrontElimination

/-- The masked literal fourth predecessor has proportional directions
in the two actual row-five reads. Eliminate it without a slope guard. -/
theorem rowFiveAffineElimination {R : Type*} [CommRing R]
    (a t m z eta : R) (ht : t+z*m=0) (ha : a+eta*z*m=0) :
    a-eta*t=0 := by
  linear_combination ha-eta*ht

/-- Eliminate one specific strict predecessor tap from a row-six
moment mask and a defect read, without assuming a noncolliding clock. -/
theorem rowSixMaskedTap {R : Type*} [CommRing R]
    (tap s h m v : R) (hs : tap*s=m) (hh : tap*h=v) :
    s*v=h*m := by
  rw [← hh,← hs]
  ring

/-- Eliminate the zero of the affine reverse multiplier from two
literal singleton-tail read equations. This makes no pole division. -/
theorem reverseRootElimination {R : Type*} [CommRing R]
    (a b c d z : R) (h₀ : b=a*z) (h₁ : d=c*z) : a*d-c*b=0 := by
  rw [h₀,h₁]
  ring

#print axioms rowFiveAffineElimination
#print axioms rowSixMaskedTap
#print axioms reverseRootElimination

end RKCert.ReviewedNative.SDIRK8GaussDoubleFrontElimination
