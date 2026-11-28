import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDssArithmeticNewStarFront

variable {K : Type*} [CommRing K]

/-- Leading and quadratic coefficients of the paid affine factor times
the genuine quadratic normalized at the two observed front singletons. -/
theorem paid_affine_factor_quadratic_coefficient
    (m₂ m₃ l₀ l₁ a b s : K)
    (h₂ : m₂=l₀*b+l₁*(a-b*s)) (h₃ : m₃=l₁*b) :
    m₂*l₁-l₁^2*a-m₃*(l₀-l₁*s)=0 := by
  rw [h₂,h₃]
  ring1

theorem four_singletons_nodal_minor (l₀ l₁ z₀ z₁ h₄ : K)
    (h₀ : l₀=h₄*z₀) (h₁ : l₁=h₄*z₁) :
    l₀*z₁-l₁*z₀=0 := by
  rw [h₀,h₁]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDssArithmeticNewStarFront
