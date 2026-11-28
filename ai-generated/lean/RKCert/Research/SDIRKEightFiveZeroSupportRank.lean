import Mathlib.Tactic.Ring

/-! Exact scalar components of the zero-support and rank classification. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroSupportRank

theorem affine_clock_factors_cannot_have_two_roots {R : Type*} [CommRing R] [IsDomain R]
    {x y la mu zx zy : R} (hne : x ≠ y) (hzx : zx ≠ 0) (hzy : zy ≠ 0)
    (h₁ : zx*(la+mu*x)=0) (h₂ : zy*(la+mu*y)=0) :
    la=0 ∧ mu=0 := by
  have hx : la+mu*x=0 := (mul_eq_zero.mp h₁).resolve_left hzx
  have hy : la+mu*y=0 := (mul_eq_zero.mp h₂).resolve_left hzy
  have h : (x-y)*mu=0 := by
    calc
      (x-y)*mu = (la+mu*x)-(la+mu*y) := by ring
      _ = 0 := by rw [hx,hy,sub_zero]
  have hmu : mu=0 := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)
  exact ⟨by simpa [hmu] using hx,hmu⟩

theorem paid_pure_adjacent_rear_forces_seven {R : Type*} [CommRing R] {v : R}
    (hκ : 1+2*v-v^2=0) (hthird : 1+4*v=0) : (7 : R)=0 := by
  have h : 16*(1+2*v-v^2)-7=(1+4*v)*(9-4*v) := by ring
  rw [hκ,hthird,mul_zero,zero_mul,zero_sub] at h
  exact neg_eq_zero.mp h

end RKResearch.Certified.SDIRKEightFiveZeroSupportRank
