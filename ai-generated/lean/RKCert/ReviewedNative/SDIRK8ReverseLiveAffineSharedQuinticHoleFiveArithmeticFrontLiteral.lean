module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticFrontLiteral

/-- The exact padded quadratic/cubic front resultant vanishes at a
literal common root, with no generic leading-coefficient assumptions. -/
theorem actualQuadraticCubicFrontProjection {R : Type*} [CommRing R]
    (s p₀ p₁ p₂ q₀ q₁ q₂ q₃ : R)
    (hp : p₀+p₁*s+p₂*s^2=0) (hq : q₀+q₁*s+q₂*s^2+q₃*s^3=0) :
    p₀^3*q₃^2-p₀^2*p₁*q₂*q₃-2*p₀^2*p₂*q₁*q₃+p₀^2*p₂*q₂^2+
      p₀*p₁^2*q₁*q₃+3*p₀*p₁*p₂*q₀*q₃-p₀*p₁*p₂*q₁*q₂-
      2*p₀*p₂^2*q₀*q₂+p₀*p₂^2*q₁^2-p₁^3*q₀*q₃+
      p₁^2*p₂*q₀*q₂-p₁*p₂^2*q₀*q₁+p₂^3*q₀^2=0 := by
  linear_combination
    (p₀^2*q₃^2-p₀*p₁*q₂*q₃-2*p₀*p₂*q₁*q₃+p₀*p₂*q₂^2+
      p₁^2*q₁*q₃+p₁*p₂*q₀*q₃-p₁*p₂*q₁*q₂-p₂^2*q₀*q₂+p₂^2*q₁^2+
      s*(-p₀*p₁*q₃^2+p₁^2*q₂*q₃-p₁*p₂*q₂^2-p₂^2*q₀*q₃+p₂^2*q₁*q₂)+
      s^2*(-p₀*p₂*q₃^2+p₁^2*q₃^2-p₁*p₂*q₂*q₃+p₂^2*q₁*q₃))*hp+
    (2*p₀*p₁*p₂*q₃-p₀*p₂^2*q₂-p₁^3*q₃+p₁^2*p₂*q₂-p₁*p₂^2*q₁+
      p₂^3*q₀+s*(p₀*p₂^2*q₃-p₁^2*p₂*q₃+p₁*p₂^2*q₂-p₂^3*q₁))*hq

#print axioms actualQuadraticCubicFrontProjection

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticFrontLiteral
