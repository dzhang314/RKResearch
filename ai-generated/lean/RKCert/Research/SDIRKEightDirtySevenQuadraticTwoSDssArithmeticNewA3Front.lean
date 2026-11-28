import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDssArithmeticNewA3Front

variable {K : Type*} [CommRing K]

theorem arithmetic_second_singleton_value (s f : K)
    (h : 2*f=1+2*s-s^2) :
    2*f-1=s*(2-s) := by
  rw [h]
  ring1

theorem paid_affine_factor_quadratic_coefficient
    (m₂ m₃ l₀ l₁ a b s : K)
    (h₂ : m₂=l₀*b+l₁*(a-b*s)) (h₃ : m₃=l₁*b) :
    m₂*l₁-l₁^2*a-m₃*(l₀-l₁*s)=0 := by
  rw [h₂,h₃]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDssArithmeticNewA3Front
