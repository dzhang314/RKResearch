module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact arithmetic of the constant-supported-trace exclusion -/

namespace RKResearch.Certified.SDIRKEightConstantZeroTrace

theorem cubic_pair_slopes {R : Type*} [CommRing R] (x y z : R) :
    (x-y)*(x-z)+(y-x)*(y-z)=(x-y)^2 := by ring

theorem only_characteristic_17 {K : Type*} [Field K] {γ : K}
    (h₅ : (5 : K) ≠ 0) (hγ : 12*γ=1)
    (hGauss : 5*(2*γ-1)^3-3*(2*γ-1)=0) :
    (17 : K)=0 := by
  have h : (5 : K)*17=0 := by
    linear_combination (180*(2*γ-1)^2-150*(2*γ-1)+17)*hγ-216*hGauss
  exact (mul_eq_zero.mp h).resolve_left h₅

theorem early_extra_reject {R : Type*} [CommRing R] [CharP R 17]
    {r₁ r₂ r₃ r₄ r₅ : R}
    (h₁ : r₁=2) (h₂ : r₂=10) (h₃ : r₃=9) (h₄ : r₄=3) (h₅ : r₅=16)
    (hread : 10*r₁+12*r₂+16*r₃+13*r₄+r₅=0) : False := by
  have hz : (339 : R)=0 := by
    rw [h₁,h₂,h₃,h₄,h₅] at hread
    linear_combination hread
  exact (by decide : ¬ (17 : ℕ) ∣ 339) ((CharP.cast_eq_zero_iff R 17 339).mp hz)

theorem late_extra_reject {R : Type*} [CommRing R] [CharP R 17]
    {r₄ r₅ : R} (h₄ : r₄=9) (h₅ : r₅=13) (hread : 10*r₄+8*r₅=8) : False := by
  have hz : (186 : R)=0 := by
    rw [h₄,h₅] at hread
    linear_combination hread
  exact (by decide : ¬ (17 : ℕ) ∣ 186) ((CharP.cast_eq_zero_iff R 17 186).mp hz)

end RKResearch.Certified.SDIRKEightConstantZeroTrace
