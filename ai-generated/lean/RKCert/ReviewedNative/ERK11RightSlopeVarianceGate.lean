/-! Denominator and variance gates for an actual two-support central alias. -/
namespace RKResearch.ERK11RightSlopeVarianceGate
open Lean.Grind

theorem twoNodeProjection {R : Type} [CommRing R]
    (H C I₀ I₁ I₂ x z : R)
    (hs : H*z=C) (hn : I₂-(x+z)*I₁+x*z*I₀=0) :
    H*I₂-C*I₁=x*(H*I₁-C*I₀) := by
  have he : I₂=(x+z)*I₁-x*z*I₀ := by grind
  rw [← hs, he]
  grind

theorem twoNodeVarianceProduct {R : Type} [CommRing R]
    (H C I₀ I₁ I₂ x z : R)
    (hs : H*z=C) (hn : I₂-(x+z)*I₁+x*z*I₀=0) :
    H*(I₀*I₂-I₁^2)=(x*I₀-I₁)*(H*I₁-C*I₀) := by
  have he : I₂=(x+z)*I₁-x*z*I₀ := by grind
  rw [← hs, he]
  grind

theorem centralDenominatorLive {K : Type} [Field K]
    (H C I₀ I₁ I₂ x z : K)
    (hs : H*z=C) (hn : I₂-(x+z)*I₁+x*z*I₀=0)
    (hH : H≠0) (hv : I₀*I₂-I₁^2≠0) :
    H*I₁-C*I₀≠0 := by
  intro hD
  have ht := twoNodeVarianceProduct H C I₀ I₁ I₂ x z hs hn
  rw [hD] at ht
  grind

end RKResearch.ERK11RightSlopeVarianceGate
#print axioms RKResearch.ERK11RightSlopeVarianceGate.twoNodeProjection
#print axioms RKResearch.ERK11RightSlopeVarianceGate.twoNodeVarianceProduct
#print axioms RKResearch.ERK11RightSlopeVarianceGate.centralDenominatorLive
