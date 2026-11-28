module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8GaussNonliteralTail

def cubic {R : Type*} [CommRing R] (a b c d x : R) : R :=
  a + b*x + c*x^2 + d*x^3

/-- The exact star tail elimination for a cubic profile has no residual
gap parameter after the three genuine distinct-clock factors. -/
theorem starCubicFactor {R : Type*} [CommRing R]
    (a b c d x γ u : R) :
    (2-u)*cubic a b c d (x-γ*u) - u*cubic a b c d (x-γ*(2-u)) +
      (1+2*u-u^2)*(2*u-2)*cubic a b c d x =
    u*(u-1)*(u-2)*(-2*cubic a b c d x - γ^2*(2*c+6*d*x) + 4*d*γ^3) := by
  unfold cubic
  ring

/-- Exact linear elimination of the unknown reverse root from the two
literal arithmetic tail comparisons. -/
theorem arithmeticProfileRootCross {K : Type*} [Field K]
    (x z c d H T k p₀ p₁ p₂ : K)
    (hx : x-z ≠ 0) (hd : d = 2*c-x)
    (h₉ : (x-z)*p₁ = k*(c-z)*p₀)
    (h₈ : H*(x-z)*p₂ = -k*T*(d-z)*p₀) :
    H*p₂+2*T*p₁-k*T*p₀=0 := by
  have h : (H*p₂+2*T*p₁-k*T*p₀)*(x-z)=0 := by
    linear_combination h₈ + 2*T*h₉ - k*T*p₀*hd
  exact (mul_eq_zero.mp h).resolve_right hx

#print axioms starCubicFactor
#print axioms arithmeticProfileRootCross

end RKCert.ReviewedNative.SDIRK8GaussNonliteralTail
