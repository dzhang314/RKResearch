module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8SilentGaussianPrefix

/-- The two rooted grade-five reads with a common earlier strict tap
eliminate that tap from the marked functional at its own clock. -/
theorem markedElimination {R : Type*} [CommRing R]
    (r rho t H LsH LrH LsXH LrXH : R)
    (h₀ : LsH-rho*LrH-t*H=0)
    (h₁ : LsXH-rho*LrXH-t*r*H=0) :
    LsXH-r*LsH=rho*(LrXH-r*LrH) := by
  linear_combination h₁-r*h₀

/-- A tapped duplicate cannot stay on a one-dimensional pure-four line
if the literal tap direction has nonzero determinant with the first row. -/
theorem duplicateTap {K : Type*} [Field K] (a t da dt k : K)
    (hunit : t*da-a*dt≠0)
    (h : t*(a+k*da)-a*(t+k*dt)=0) : k=0 := by
  have e : k*(t*da-a*dt)=0 := by linear_combination h
  exact (mul_eq_zero.mp e).resolve_right hunit

#print axioms markedElimination
#print axioms duplicateTap

end RKCert.ReviewedNative.SDIRK8SilentGaussianPrefix
