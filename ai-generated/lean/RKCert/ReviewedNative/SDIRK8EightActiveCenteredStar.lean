module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveCenteredStar

/-- The affine reverse multiplier is determined by the terminal read
and the mean of the two symmetric live rear reads. No tail defect is
assumed nonzero, so this also applies at an actual Gauss-tail contact. -/
theorem centeredAffineShape {R : Type*} [CommRing R]
    (x mid g v p₀ p₁ κ scale y h₀ h₁ h₂ : R)
    (hx : h₀=scale*(p₀+p₁*x))
    (hc : h₁=scale*κ*(p₀+p₁*(mid-g*v)))
    (hd : h₂=scale*κ*(p₀+p₁*(mid+g*v))) :
    2*(y-mid)*κ*h₀+(x-y)*(h₁+h₂)=
      2*scale*κ*(x-mid)*(p₀+p₁*y) := by
  rw [hx, hc, hd]
  ring

/-- The centered pair is represented by a quadratic with the exact
leading coefficient of the affine gap equation; no variable
denominator occurs in the two physical peg factors. -/
theorem homogeneousCenteredPair {R : Type*} [CommRing R]
    (a b g mid v X : R) (h : a+b*v^2=0) :
    b*(X-(mid-g*v))*(X-(mid+g*v))=b*(X-mid)^2+a*g^2 := by
  linear_combination -g^2*h

#print axioms centeredAffineShape
#print axioms homogeneousCenteredPair

end RKCert.ReviewedNative.SDIRK8EightActiveCenteredStar
