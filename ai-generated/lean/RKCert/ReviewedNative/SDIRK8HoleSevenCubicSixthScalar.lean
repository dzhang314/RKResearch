module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8HoleSevenCubicSixthScalar

/-- Combining both actual sixth-clock coefficients when its slope vanishes
yields the scaled fixed-amplitude identity. No reconstructed clock is used. -/
theorem zeroSixthSlope {K : Type*} [Field K] [CharZero K]
    (a b γ d l₀ l₁ : K) (hg : γ≠0)
    (h₁ : a*γ^2*(8*d-9*l₁)-8*b=0)
    (h₀ : a*γ^3*(-56*d-9*l₀)+56*b*γ+72*γ^2=0) :
    a*γ*(l₀+7*l₁)=8 := by
  have hp : γ^2*(a*γ*(l₀+7*l₁)-8)=0 := by
    linear_combination (-1/9:K)*h₀-(7/9:K)*γ*h₁
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hg))

/-- Combine true penultimate and terminal equations without dividing by a
clock gap. The actual terminal amplitude is the only factor canceled. -/
theorem visibilityFreeTerminal {R : Type*} [CommRing R] [NoZeroDivisors R]
    (Hc Hx xz cz Pc Px k : R) (hx : Hx≠0)
    (hp : xz*Hc=k*cz*Hx) (ht : Hc*Pc+Hx*Px=0) :
    k*(cz*Pc)+(xz*Px)=0 := by
  have h : Hx*(k*(cz*Pc)+(xz*Px))=0 := by
    linear_combination xz*ht-Pc*hp
  exact (mul_eq_zero.mp h).resolve_left hx

end RKCert.ReviewedNative.SDIRK8HoleSevenCubicSixthScalar
