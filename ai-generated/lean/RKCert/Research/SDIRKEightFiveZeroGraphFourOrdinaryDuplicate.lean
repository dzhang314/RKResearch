import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! A native scalar/cardinal moment step for a quadratic-zero duplicate. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroGraphFourOrdinaryDuplicate
open scoped BigOperators

theorem singleton_pure_value_zero_of_cubic_moment
    {R ι : Type*} [CommRing R] [IsDomain R] [Fintype ι] [DecidableEq ι]
    (b c f : ι → R) (j : ι) (x₁ x₂ x₃ : R)
    (hb : b j ≠ 0)
    (h₁ : c j ≠ x₁) (h₂ : c j ≠ x₂) (h₃ : c j ≠ x₃)
    (hcover : ∀ i, i ≠ j → b i ≠ 0 → c i=x₁ ∨ c i=x₂ ∨ c i=x₃)
    (hm : ∑ i, b i*((c i-x₁)*(c i-x₂)*(c i-x₃))*f i = 0) :
    f j = 0 := by
  have hother (i : ι) (hi : i ≠ j) :
      b i*((c i-x₁)*(c i-x₂)*(c i-x₃))*f i=0 := by
    by_cases hbi : b i=0
    · simp [hbi]
    · rcases hcover i hi hbi with hc | hc | hc <;> simp [hc]
  have htotal :
      (∑ i, b i*((c i-x₁)*(c i-x₂)*(c i-x₃))*f i) =
        b j*((c j-x₁)*(c j-x₂)*(c j-x₃))*f j := by
    exact Finset.sum_eq_single j (fun i _ hi => hother i hi) (by simp)
  rw [htotal] at hm
  exact (mul_eq_zero.mp hm).resolve_left
    (mul_ne_zero hb (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h₁) (sub_ne_zero.mpr h₂))
      (sub_ne_zero.mpr h₃)))

theorem supported_duplicate_clock_cut {R : Type*} [CommRing R] {a x p q : R}
    (hx : x=a) : (x-a)*p+(x-a)*q=0 := by simp [hx]

end RKResearch.Certified.SDIRKEightFiveZeroGraphFourOrdinaryDuplicate
