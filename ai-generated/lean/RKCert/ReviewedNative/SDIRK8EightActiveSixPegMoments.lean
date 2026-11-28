module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveSixPegMoments

/-- The signed six-peg mask leaves two genuine clocks. The
coefficient form of their two moment equations is usable without
dividing the Hankel, even when a reduced specialization degenerates. -/
theorem scaledMissingQuadratic {R : Type*} [CommRing R]
    (m₀ m₁ m₂ m₃ s₀ s₁ : R)
    (h₀ : m₀*s₀+m₁*s₁+m₂=0)
    (h₁ : m₁*s₀+m₂*s₁+m₃=0) :
    (m₀*m₂-m₁^2)*s₀=m₁*m₃-m₂^2 ∧
    (m₀*m₂-m₁^2)*s₁=m₁*m₂-m₀*m₃ := by
  constructor
  · linear_combination m₂*h₀-m₁*h₁
  · linear_combination m₀*h₁-m₁*h₀

#print axioms scaledMissingQuadratic

end RKCert.ReviewedNative.SDIRK8EightActiveSixPegMoments
