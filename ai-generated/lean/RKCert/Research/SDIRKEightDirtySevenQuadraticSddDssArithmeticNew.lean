import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddDssArithmeticNew

variable {K : Type*} [CommRing K]

theorem graph_ratio_cubic (v w₀ w₁ w₂ : K) :
    (-2+v+4*v^2-v^3)*(w₁-3*w₂*v) -
      (v-2)*(3*v-2)*(w₀-w₁*v+w₂*v^2) =
    (2*w₁-4*w₂)*v^3 + (-3*w₀-4*w₁-7*w₂)*v^2 +
      (8*w₀+5*w₁+6*w₂)*v - 2*w₁ - 4*w₀ := by
  ring1

theorem two_paid_front_D_fits (a b p q J : K)
    (ha : a=J*p) (hb : b=J*q) :
    p*b-q*a=0 := by
  rw [ha,hb]
  ring1

theorem scaled_terminal_D (k mu L g r Z J : K)
    (h : 2*k*g=mu) :
    mu*(4*k^2*L-2*k*Z-J*(mu-2*k*r)) =
      4*k^2*(mu*L-g*Z-J*g*(g-r)) := by
  rw [← h]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddDssArithmeticNew
