module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8NonliteralSixSeven

open Polynomial

/-- The two reflected star reads are linear in the actual reverse site.
Eliminate it without requiring an inverse of either centered gap slope. -/
theorem eliminateStarReverseClock
    {K : Type*} [Field K] (qx q₁ γ l k e o w : K) (hl : l * k ≠ 0)
    (he : (qx * e + l * k * q₁) * w + l * k * (qx - γ * q₁) = 0)
    (ho : qx * o * w - l * k * γ * q₁ = 0) :
    (qx * e + l * k * q₁) * γ * q₁ +
      (qx - γ * q₁) * qx * o = 0 := by
  have h : l * k * ((qx * e + l * k * q₁) * γ * q₁ +
      (qx - γ * q₁) * qx * o) = 0 := by
    linear_combination (qx * o) * he - (qx * e + l * k * q₁) * ho
  exact (mul_eq_zero.mp h).resolve_left hl

/-- The actual fourth and actual fifth are distinct ordinary nodes.
A known fourth root removes only its own linear nodal factor. -/
theorem ordinaryFifthAfterFourthFactor
    {K : Type*} [Field K] (p q : K[X]) (s y r : K)
    (h : p = (X - C s) * q + C r) (hs : p.eval s = 0)
    (hy : p.eval y = 0) (hne : y ≠ s) :
    q.eval y = 0 := by
  have hr : r = 0 := by simpa [h] using hs
  have h' : (y - s) * q.eval y = 0 := by
    simpa only [h, eval_add, eval_mul, eval_sub, eval_X, eval_C, hr, add_zero] using hy
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)

end RKCert.ReviewedNative.SDIRK8NonliteralSixSeven

#print axioms RKCert.ReviewedNative.SDIRK8NonliteralSixSeven.eliminateStarReverseClock
#print axioms RKCert.ReviewedNative.SDIRK8NonliteralSixSeven.ordinaryFifthAfterFourthFactor
