module

public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8NonliteralEighth

/-- The physical silent eighth geometry eliminates its actual reverse
clock from the ninth/terminal ordinary ratio. No cubic amplitude of
the silent eighth is assumed nonzero. -/
theorem silentEighthNinthRatio
    {K : Type*} [Field K] (γ u x z k qx qc lx lc : K)
    (h : γ * k ≠ 0)
    (hz : 2 * (z - x) = γ * k * (u - 2))
    (hn : qx * (x - z) * lc - k * qc * (x - γ * u - z) * lx = 0) :
    (u - 2) * lc * qx - (2*u + k*(u-2)) * lx * qc = 0 := by
  have hz' := sub_eq_zero.mpr hz
  have h' : γ * k * ((u - 2) * lc * qx - (2*u + k*(u-2)) * lx * qc) = 0 := by
    linear_combination -(2 : K) * hn - (qx * lc - k * qc * lx) * hz'
  exact (mul_eq_zero.mp h').resolve_left h

/-- An actual chronological read affine in a prior amplitude can be
crossed with any separate affine amplitude read; its coefficient need
not be a unit, before or after reduction. -/
theorem affineContinuationCross
    {R : Type*} [CommRing R] (F₀ F₁ q p h : R)
    (hF : F₀ + F₁ * h = 0) (hRead : q * h = p) :
    q * F₀ + p * F₁ = 0 := by
  have hRead' := sub_eq_zero.mpr hRead
  linear_combination q * hF - F₁ * hRead'

end RKCert.ReviewedNative.SDIRK8NonliteralEighth

#print axioms RKCert.ReviewedNative.SDIRK8NonliteralEighth.silentEighthNinthRatio


#print axioms RKCert.ReviewedNative.SDIRK8NonliteralEighth.affineContinuationCross
