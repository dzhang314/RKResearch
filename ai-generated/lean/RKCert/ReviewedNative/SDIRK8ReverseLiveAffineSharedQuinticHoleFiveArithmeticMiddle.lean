module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticMiddle

/-- Both necessary monic six-peg cuts use the actual one-root cofactor.
There is no inversion at a possible shared signed moment rank drop. -/
theorem monicSignedSixPegCuts {R : Type*} [CommRing R]
    (n m₀ m₁ m₂ m₃ ν₄ ν₅ e₅ H₃ H₄ : R)
    (h₁ : m₁-n*m₀=0) (h₂ : ν₄=H₄*(m₂-n*m₁))
    (h₃ : (e₅-n)*ν₄+ν₅-H₃*(m₂-n*m₁)-H₄*(m₃-n*m₂)=0) :
    H₄*(m₀*m₂-m₁^2)-ν₄*m₀=0 ∧
      (H₄*(e₅*ν₄+ν₅)-H₃*ν₄)*m₀-H₄*ν₄*m₁-H₄^2*(m₀*m₃-m₁*m₂)=0 := by
  constructor
  · linear_combination -m₀*h₂-H₄*m₁*h₁
  · linear_combination H₄*m₀*h₃-H₃*m₀*h₂+(H₄^2*m₂-H₄*ν₄)*h₁

/-- The padded quadratic resultant vanishes at a common literal root,
including every leading coefficient drop of either quadratic. -/
theorem quadraticPairProjection {R : Type*} [CommRing R]
    (s p₀ p₁ p₂ q₀ q₁ q₂ : R)
    (hp : p₀+p₁*s+p₂*s^2=0) (hq : q₀+q₁*s+q₂*s^2=0) :
    (p₂*q₀-p₀*q₂)^2-(p₂*q₁-p₁*q₂)*(p₁*q₀-p₀*q₁)=0 := by
  have ha : (p₂*q₀-p₀*q₂)+(p₂*q₁-p₁*q₂)*s=0 := by
    linear_combination p₂*hq-q₂*hp
  have hb : (p₁*q₀-p₀*q₁)-(p₂*q₁-p₁*q₂)*s^2=0 := by
    linear_combination p₁*hq-q₁*hp
  linear_combination ((p₂*q₀-p₀*q₂)-(p₂*q₁-p₁*q₂)*s)*ha-(p₂*q₁-p₁*q₂)*hb

#print axioms monicSignedSixPegCuts
#print axioms quadraticPairProjection

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticMiddle
