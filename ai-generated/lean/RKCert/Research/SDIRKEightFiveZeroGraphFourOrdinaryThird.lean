import Mathlib.Tactic.Ring

/-! Scalar supported-clock reads through grade five. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroGraphFourOrdinaryThird

theorem weighted_second_power_from_two_taps {R : Type*} [CommRing R]
    {a b p q d₀ d₁ : R}
    (h₀ : p+q=d₀) (h₁ : a*p+b*q=d₁) :
    a^2*p+b^2*q=(a+b)*d₁-a*b*d₀ := by
  rw [←h₀,←h₁]
  ring

theorem two_gauss_fifth_grade_reads {R : Type*} [CommRing R]
    {d₁ d₂ ℓ₁ ℓ₂ beta : R}
    (h₁ : d₁=beta*ℓ₁) (h₂ : d₂=beta*ℓ₂) :
    ℓ₁*d₂-ℓ₂*d₁=0 := by
  rw [h₁,h₂]
  ring

end RKResearch.Certified.SDIRKEightFiveZeroGraphFourOrdinaryThird
