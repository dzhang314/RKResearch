module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticStarFourth

/-- Eliminate the paid centered gap w while retaining the actual fourth
clock γ*s in the affine comparison. No pivot is inverted. -/
theorem trueFourthCenteredAffineRead {R : Type*} [CommRing R]
    (x γ s w F₀ F₁ L₀ L₁ Hx : R) (hF : F₀+F₁*w=0)
    (hO : (x-γ*s)*(L₀+L₁*w)+γ*(2-w)*Hx=0) :
    (x-γ*s)*(F₁*L₀-F₀*L₁)+γ*Hx*(2*F₁+F₀)=0 := by
  linear_combination F₁*hO-((x-γ*s)*L₁-γ*Hx)*hF

/-- The actual affine fourth coefficient cannot vanish. The true nonzero
factors are diagonal, terminal amplitude, gap and F₁. -/
theorem trueFourthAffineCoefficient {R : Type*} [CommRing R] [NoZeroDivisors R]
    (x γ s A Hx k F₁ : R)
    (hγ : γ≠0) (hHx : Hx≠0) (hk : k≠0) (hF₁ : F₁≠0)
    (h : (x-γ*s)*A+γ*Hx*k*F₁=0) :
    A≠0 := by
  intro hA
  have hh : γ*Hx*k*F₁=0 := by simpa [hA] using h
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hγ hHx) hk) hF₁) hh

#print axioms trueFourthCenteredAffineRead
#print axioms trueFourthAffineCoefficient

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticStarFourth
