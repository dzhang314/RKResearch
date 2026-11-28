module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ArithmeticLiteralFourthProfilePivot

/-- The actual ordinary-silent clock is fixed by the affine tail comparison.
After the true factor u is removed, L is nonzero at that tableau.
No assumption is made about the value of the profile at the silent clock. -/
theorem silentClockHomogeneous {K : Type*} [CommRing K] [NoZeroDivisors K]
    (g u k x c z s Hc Hx L : K)
    (hg : g≠0) (hu : u≠0) (hk : k≠0) (hHx : Hx≠0)
    (hc : c=x-g*u) (hz : z=g*s) (hL : Hc-k*Hx=u*L)
    (ha : (x-z)*Hc=k*(c-z)*Hx) :
    L≠0 ∧ g*L*s=x*L+g*k*Hx := by
  have h₀ : u*((x-z)*L+g*k*Hx)=0 := by
    linear_combination ha - (x-z)*hL + k*Hx*hc
  have h₁ := (mul_eq_zero.mp h₀).resolve_left hu
  constructor
  · intro h
    rw [h, mul_zero, zero_add] at h₁
    exact mul_ne_zero (mul_ne_zero hg hk) hHx h₁
  · rw [hz] at h₁
    linear_combination -h₁

/-- Substitute the forced silent clock into an actual fourth cubic
without adding a denominator to the polynomial projection. -/
theorem homogeneousCubic {R : Type*} [CommRing R]
    (n d s c₀ c₁ c₂ c₃ : R)
    (hs : d*s=n) (h : c₀+c₁*s+c₂*s^2+c₃*s^3=0) :
    c₀*d^3+c₁*n*d^2+c₂*n^2*d+c₃*n^3=0 := by
  rw [← hs]
  linear_combination d^3*h

#print axioms silentClockHomogeneous
#print axioms homogeneousCubic

end RKCert.ReviewedNative.SDIRK8ArithmeticLiteralFourthProfilePivot
