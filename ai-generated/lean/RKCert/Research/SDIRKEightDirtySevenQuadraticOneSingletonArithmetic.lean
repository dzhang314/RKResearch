import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticOneSingletonArithmetic

variable {K : Type*} [CommRing K]

/-- The leading numerator of the unique three-singleton arithmetic fit.
The field proof uses the genuine nonzero arithmetic denominator. -/
theorem graph_leading_numerator (u : K) :
    -(-2+u+4*u^2-u^3)+2*(3*u-2) = (u-1)^2*(u-2) := by
  ring1

/-- The fitted graph at the actual arithmetic third coordinate. -/
theorem graph_third_value_clear (u D : K) :
    D*(1+2*(2*u)-(2*u)^2) + 2*(3*u-2)*(2*u)*(2*u-u) =
      (1+4*u-4*u^2)*D+4*u^2*(3*u-2) := by
  ring1

theorem monic_quadratic_product_remainder (y w₁ w₀ a₀ a₁ b₀ b₁ : K) :
    (a₀+a₁*y)*(b₀+b₁*y) =
      a₁*b₁*(y^2+w₁*y+w₀) +
      ((a₀*b₀-w₀*a₁*b₁)+(a₀*b₁+a₁*b₀-w₁*a₁*b₁)*y) := by
  ring1

/-- The two projection equations at opposite clocks force its affine
intercept to vanish. The actual even Legendre value is nonzero by coprimality. -/
theorem opposite_roots_force_zero_intercept [IsDomain K]
    (a b z l₃ l₄ : K) (h₂ : (2 : K) ≠ 0) (he : l₄ ≠ 0)
    (hp : l₃ - (a+b*z)*l₄ = 0)
    (hm : -l₃ - (a-b*z)*l₄ = 0) : a = 0 := by
  have hh : 2*a*l₄ = 0 := by
    calc
      _ = -(l₃ - (a+b*z)*l₄) - (-l₃ - (a-b*z)*l₄) := by ring1
      _ = 0 := by rw [hp, hm]; ring1
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right he)).resolve_left h₂

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticOneSingletonArithmetic
