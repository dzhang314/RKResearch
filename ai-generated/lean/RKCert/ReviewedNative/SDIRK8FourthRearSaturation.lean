module

public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8FourthRearSaturation

/-- Cancel the homogeneous factor of the star-tail cross before constructing
a diagonal resultant. The hypothesis is on the true tableau guard, not on a
particular finite residue of that guard. -/
theorem starAffineGuardedCross
    {K : Type*} [Field K] (d l p₀ p₁ p₂ p₃ b₀ b₁ V : K)
    (hd : d ≠ 0)
    (he : d * (p₀ + p₂ * V) + l * (2 - V) * b₀ = 0)
    (ho : d * (p₁ + p₃ * V) + l * (2 - V) * b₁ = 0) :
    d * (p₀ * p₃ - p₂ * p₁) +
      l * (b₀ * (2 * p₃ + p₁) - b₁ * (p₀ + 2 * p₂)) = 0 := by
  have h : d * (d * (p₀ * p₃ - p₂ * p₁) +
      l * (b₀ * (2 * p₃ + p₁) - b₁ * (p₀ + 2 * p₂))) = 0 := by
    linear_combination (d * p₃ - l * b₁) * he - (d * p₂ - l * b₀) * ho
  exact (mul_eq_zero.mp h).resolve_left hd

end RKCert.ReviewedNative.SDIRK8FourthRearSaturation

#print axioms RKCert.ReviewedNative.SDIRK8FourthRearSaturation.starAffineGuardedCross
