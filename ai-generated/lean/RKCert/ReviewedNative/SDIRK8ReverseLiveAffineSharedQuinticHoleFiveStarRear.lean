module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarRear

/-- The second physical star comparison follows from the first and the
star-tail grade-three read: its only cancellation is the true gap 1+v. -/
theorem bothActualStarComparisons {F : Type*} [Field F]
    (v g X z Hc Hd Hx k : F) (hu : 1+v ≠ 0)
    (hc : (X+g-z)*Hc-k*(X-g*v-z)*Hx=0)
    (hstar : (1-v)*Hc-(1+v)*Hd+2*v*k*Hx=0) :
    (X+g-z)*Hd-k*(X+g*v-z)*Hx=0 := by
  apply (mul_eq_zero.mp ?_).resolve_left hu
  linear_combination (1-v)*hc-(X+g-z)*hstar

/-- Centering the two comparisons yields their sum and their divided odd
read. No division by a coefficient of the unknown profile is needed. -/
theorem centeredSymmetricReads {R : Type*} [CommRing R]
    (v g X z Hc Hd Hx k : R)
    (hc : (X+g-z)*Hc-k*(X-g*v-z)*Hx=0)
    (hd : (X+g-z)*Hd-k*(X+g*v-z)*Hx=0) :
    ((X+g-z)*(Hc+Hd)-2*k*(X-z)*Hx=0) ∧
      ((X+g-z)*(Hc-Hd)+2*g*v*k*Hx=0) := by
  constructor
  · linear_combination hc+hd
  · linear_combination hc-hd

/-- The two centered affine conditions give a homogeneous elimination that
remains valid at any specialization of their coefficients. -/
theorem centeredAffineNecessary {R : Type*} [CommRing R]
    (w F0 F1 O0 O1 : R) (hF : F0+F1*w=0) (hO : O0+O1*w=0) :
    F1*O0-F0*O1=0 := by
  linear_combination F1*hO-O1*hF

#print axioms bothActualStarComparisons
#print axioms centeredSymmetricReads
#print axioms centeredAffineNecessary

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarRear
