import Mathlib.Tactic.Ring.Basic

/-!
Paid SDIRK8 physical row-two scalar gate. A zero at the second row is
impossible under the extracted clean cubic read. That read is valid when
the actual quadratic residual is supported at two different clocks;
it is not assumed at a one-off-clock saturated tableau.
-/

namespace RKResearch.Certified.SDIRKEightMultiClockRowTwo

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Two nonzero residuals at different clocks detect both affine
coefficients. This is the elementary rank-two test for GE₁. -/
theorem affine_residual_detects
    {g₀ g₁ c₀ c₁ u v : R} (hg₀ : g₀≠0) (hg₁ : g₁≠0) (hc : c₀≠c₁)
    (h₀ : g₀*(u+v*c₀)=0) (h₁ : g₁*(u+v*c₁)=0) :
    u=0 ∧ v=0 := by
  have e₀ := (mul_eq_zero.mp h₀).resolve_left hg₀
  have e₁ := (mul_eq_zero.mp h₁).resolve_left hg₁
  have hp : v*(c₀-c₁)=0 := by
    calc
      _ = (u+v*c₀)-(u+v*c₁) := by ring1
      _ = _ := by rw [e₀,e₁,sub_self]
  have hv := (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hc)
  exact ⟨by simpa only [hv,zero_mul,add_zero] using e₀, hv⟩

/-- Here t is the first strict tap at physical row two, and d₁,d₂
are the *doubled* residuals at physical rows one and two. The clean
cubic implication supplied by the grade-three flag is the only order
hypothesis in this division-free statement. -/
theorem second_doubled_residual_ne_zero
    {γ t x d₁ d₂ : R} (hγ : γ≠0) (hx : x=γ+t)
    (h₁ : d₁=γ^2) (h₂ : d₂=2*(t*γ+γ*x)-x^2)
    (clean : d₂=0 → t*d₁+γ*d₂=0) :
    d₂≠0 := by
  intro hz
  have hm := clean hz
  rw [hz,mul_zero,add_zero,h₁] at hm
  have ht := (mul_eq_zero.mp hm).resolve_right (pow_ne_zero 2 hγ)
  have he : d₂=γ^2 := by rw [h₂,hx,ht]; ring1
  exact (pow_ne_zero 2 hγ) (he.symm.trans hz)

/-- The zero-ratio literal front equation localizes the support in
the separate one-clock chart, instead of asserting a clean cubic row. -/
theorem front_zero_ratio_localizes
    {γ c g κ h : R} (hg : g≠0) (hk : κ=0)
    (hRead : (c-γ)*g=κ*h) : c=γ := by
  rw [hk,zero_mul] at hRead
  exact sub_eq_zero.mp ((mul_eq_zero.mp hRead).resolve_right hg)

end RKResearch.Certified.SDIRKEightMultiClockRowTwo
