import Mathlib.Tactic.Ring

/-! Native coefficient checks for a primitive divisible by its own quadratic. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroGraphFourOff

private theorem nonzero_constant_forces_unit_linear {R : Type*} [CommRing R] [IsDomain R]
    {p₀ p₁ a b : R} (hn : p₀ ≠ 0)
    (h₁ : p₁*b+p₀*a=p₀) (h₀ : p₀*b=0) : a=1 := by
  have hb := (mul_eq_zero.mp h₀).resolve_left hn
  have h : p₀*a=p₀ := by simpa [hb] using h₁
  have he : p₀*(a-1)=0 := by rw [mul_sub,mul_one,h,sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hn)

theorem affine_divides_primitive_is_monomial {R : Type*} [CommRing R] [IsDomain R]
    {p₀ p₁ a b : R} (hp : p₁ ≠ 0)
    (h₂ : 2*p₁*a=p₁) (h₁ : p₁*b+p₀*a=p₀) (h₀ : p₀*b=0) :
    p₀=0 := by
  by_contra hn
  have ha := nonzero_constant_forces_unit_linear hn h₁ h₀
  rw [ha,mul_one] at h₂
  apply hp
  calc
    p₁ = 2*p₁-p₁ := by ring
    _ = 0 := by rw [h₂,sub_self]

theorem quadratic_divides_primitive_is_monomial {R : Type*} [CommRing R] [IsDomain R]
    {p₀ p₁ p₂ a b : R} (h₂unit : (2 : R) ≠ 0) (hp : p₂ ≠ 0)
    (h₃ : 3*p₂*a=p₂) (h₂ : 2*(p₁*a+p₂*b)=p₁)
    (h₁ : p₁*b+p₀*a=p₀) (h₀ : p₀*b=0) : p₀=0 ∧ p₁=0 := by
  have ez : p₀=0 := by
    by_contra hn
    have ha := nonzero_constant_forces_unit_linear hn h₁ h₀
    have hh : 3*p₂ = p₂ := by simpa [ha] using h₃
    have hbad : (2 : R)*p₂=0 := by
      calc
        2*p₂ = 3*p₂-p₂ := by ring
        _ = 0 := by rw [hh,sub_self]
    exact (mul_ne_zero h₂unit hp) hbad
  refine ⟨ez,?_⟩
  have e₁ : p₁*b=0 := by simpa [ez] using h₁
  by_contra hn
  have hb := (mul_eq_zero.mp e₁).resolve_left hn
  have he₂ : 2*(p₁*a)=p₁ := by simpa [hb] using h₂
  have h₂' : (2*a-1)*p₁=0 := by
    calc
      (2*a-1)*p₁ = 2*(p₁*a)-p₁ := by ring
      _ = 0 := by rw [he₂,sub_self]
  have h₃' : (3*a-1)*p₂=0 := by
    calc
      (3*a-1)*p₂ = 3*p₂*a-p₂ := by ring
      _ = 0 := by rw [h₃,sub_self]
  have ha₂ := (mul_eq_zero.mp h₂').resolve_right hn
  have ha₃ := (mul_eq_zero.mp h₃').resolve_right hp
  apply one_ne_zero (α := R)
  calc
    (1 : R) = 2*(3*a-1)-3*(2*a-1) := by ring
    _ = 0 := by rw [ha₃,ha₂]; simp

end RKResearch.Certified.SDIRKEightFiveZeroGraphFourOff
