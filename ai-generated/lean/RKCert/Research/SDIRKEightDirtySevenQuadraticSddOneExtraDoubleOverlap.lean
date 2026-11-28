import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddOneExtraDoubleOverlap

variable {K : Type*} [CommRing K]

/-- Eliminate the true reverse residual scale without an extra affine pivot. -/
theorem paid_singleton_eliminates_scale
    (m₀ ms rho s e lam f₀ f₁ : K)
    (hf : f₀ = lam*f₁)
    (hl : 2*m₀*rho*(s-e)*lam = -(e*ms)) :
    2*m₀*rho*(s-e)*f₀+e*ms*f₁ = 0 := by
  rw [hf]
  calc
    _ = (2*m₀*rho*(s-e)*lam)*f₁+(e*ms)*f₁ := by ring1
    _ = 0 := by rw [hl]; ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddOneExtraDoubleOverlap
