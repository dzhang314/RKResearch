import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddDdd

variable {K : Type*} [CommRing K]

/-- Clearing the actual three Legendre denominators preserves
the affine projection condition. -/
theorem affine_legendre_collinearity
    (a b t₀ t₁ t₂ j₀ j₁ j₂ l₀ l₁ l₂ : K)
    (h₀ : j₀ = (a+b*t₀)*l₀) (h₁ : j₁ = (a+b*t₁)*l₁)
    (h₂ : j₂ = (a+b*t₂)*l₂) :
    (j₁*l₀-j₀*l₁)*l₂*(t₂-t₀) - (j₂*l₀-j₀*l₂)*l₁*(t₁-t₀) = 0 := by
  rw [h₀,h₁,h₂]
  ring1

/-- Two paid D overlaps have the same common Vieta factor,
even without cancelling the unknown scale. -/
theorem two_true_overlap_products (L₁ L₂ b lam f₁ f₂ r₁ r₂ : K)
    (h₁ : L₁ = -(b*lam*f₁*r₁)) (h₂ : L₂ = -(b*lam*f₂*r₂)) :
    L₁*f₂*r₂-L₂*f₁*r₁=0 := by
  rw [h₁,h₂]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddDdd
