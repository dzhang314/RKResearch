import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDssArithmeticNewA2Ingress

variable {K : Type*} [CommRing K]

theorem arithmetic_third_half_amplitude (d : K) :
    (1+4*d-4*d^2)*(-2+d+4*d^2-d^3)+4*d^2*(3*d-2)
       -(-2+d+4*d^2-d^3)=4*d*(d-2)*(d^3-3*d^2+1) := by
  ring1

theorem paid_affine_factor_quadratic_coefficient
    (m₂ m₃ l₀ l₁ a b s : K)
    (h₂ : m₂=l₀*b+l₁*(a-b*s)) (h₃:m₃=l₁*b) :
    m₂*l₁-l₁^2*a-m₃*(l₀-l₁*s)=0 := by
  rw [h₂,h₃]
  ring1

theorem rear_arithmetic_equal_defects (v : K) :
    (1+4*v-4*v^2)*(-2+v+4*v^2-v^3)+4*v^2*(3*v-2)
       -(1+2*v-v^2)*(-2+v+4*v^2-v^3) =
       -v*(1+2*v-v^2)*(v-2)*(3*v-2) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDssArithmeticNewA2Ingress
