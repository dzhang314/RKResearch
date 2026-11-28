module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ArithmeticLiteralThirdProfilePivot

/-- Eliminate only the affine profile coordinate, without assuming
either of the tail-read coefficient pivots is nonzero. -/
theorem affineProfileCompatibility {R : Type*} [CommRing R]
    (eta f₀ f₁ g₀ g₁ p v : R)
    (hf : f₀ + eta*f₁ = 0) (hg : g₀ + eta*g₁ = 0)
    (hfour : eta*v = p) :
    f₀*g₁-f₁*g₀=0 ∧ g₁*p+g₀*v=0 := by
  constructor
  · linear_combination g₁*hf-f₁*hg
  · linear_combination v*hg-g₁*hfour

/-- The G-pivot profile is exactly a scalar multiple of the actual
profile, coefficient by coefficient. No denominator is introduced. -/
theorem affineProfileScale {R : Type*} [CommRing R]
    (eta g₀ g₁ h₀ h₁ : R) (hg : g₀+eta*g₁=0) :
    g₁*h₀-g₀*h₁=g₁*(h₀+eta*h₁) := by
  linear_combination -h₁*hg

/-- The exact two-site gap relation cannot hold at both distinct
literal silent clocks. This is not a swapped chronology. -/
theorem distinctLiteralSilentClocksNotSimultaneous
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (a b x c k Hc Hx : R) (hab : b≠a) (hxc : x≠c)
    (hk : k≠0) (hH : Hx≠0)
    (ha : (x-a)*Hc=k*(c-a)*Hx)
    (hb : (x-b)*Hc=k*(c-b)*Hx) : False := by
  have h₀ : (b-a)*(Hc-k*Hx)=0 := by
    linear_combination ha-hb
  have h₁ := (mul_eq_zero.mp h₀).resolve_left (sub_ne_zero.mpr hab)
  have h₂ : (x-c)*(k*Hx)=0 := by
    linear_combination ha-(x-a)*h₁
  exact (mul_ne_zero (sub_ne_zero.mpr hxc) (mul_ne_zero hk hH)) h₂

#print axioms affineProfileCompatibility
#print axioms affineProfileScale
#print axioms distinctLiteralSilentClocksNotSimultaneous

end RKCert.ReviewedNative.SDIRK8ArithmeticLiteralThirdProfilePivot
