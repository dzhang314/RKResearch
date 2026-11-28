module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8OneFrontZeroTailPin

/-- A nonzero anchored value and two distinct literal tail clocks
justify the exact affine-profile solve. In particular the scalar
tail coefficient cannot be divided on a merely generic branch. -/
theorem anchoredTailSlopeUnit {K : Type*} [Field K]
    (a c d s t q₀ q₁ : K)
    (hc : c ≠ d) (hs : s ≠ 0) (ha : q₀+q₁*a ≠ 0)
    (h : s*(q₀+q₁*c)+t*(q₀+q₁*d)=0) :
    s*(c-a)+t*(d-a) ≠ 0 := by
  intro hzero
  have h' : (s+t)*(q₀+q₁*a)=0 := by
    linear_combination h-q₁*hzero
  have hz := (mul_eq_zero.mp h').resolve_right ha
  have h'' : s*(c-d)=0 := by
    linear_combination hzero-(d-a)*hz
  exact (mul_ne_zero hs (sub_ne_zero.mpr hc)) h''

/-- The homogeneous gauge of that same affine-profile solve, which
allows row-five polynomials to be formed without a field division
in the diagonal parameter. -/
theorem anchoredTailHomogeneous {R : Type*} [CommRing R]
    (a c d s t q₀ q₁ A : R)
    (ha : A=q₀+q₁*a)
    (h : s*(q₀+q₁*c)+t*(q₀+q₁*d)=0) :
    q₁*(s*(c-a)+t*(d-a))=-A*(s+t) := by
  linear_combination h+(s+t)*ha

#print axioms anchoredTailSlopeUnit
#print axioms anchoredTailHomogeneous

end RKCert.ReviewedNative.SDIRK8OneFrontZeroTailPin
