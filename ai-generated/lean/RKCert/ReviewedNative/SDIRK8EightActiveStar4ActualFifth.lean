module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveStar4ActualFifth

/-- Fold the actual unordered rear pair after homogenizing the square
gap. No square root or inverse of the gap coefficient is needed. -/
theorem foldedPairProjection {R : Type*} [CommRing R]
    (a b w x m g : R) (h : a+b*w=0) :
    b*((x-m)^2-g^2*w)=b*(x-m)^2+g^2*a := by
  linear_combination -g^2*h

/-- Exact quotients of the literal three-tap Vandermonde denominators,
before reduction and without inverting the actual fourth differences. -/
theorem clearedLiteralTapWeights {R : Type*} [CommRing R]
    (a b s : R) :
    (b-a)*(s-a)*(s-b) = (s-b)*((a-b)*(a-s)) ∧
    (b-a)*(s-a)*(s-b) = (a-s)*((b-a)*(b-s)) ∧
    (b-a)*(s-a)*(s-b) = (b-a)*((s-a)*(s-b)) := by
  constructor
  · ring
  constructor <;> ring

#print axioms foldedPairProjection
#print axioms clearedLiteralTapWeights

end RKCert.ReviewedNative.SDIRK8EightActiveStar4ActualFifth
