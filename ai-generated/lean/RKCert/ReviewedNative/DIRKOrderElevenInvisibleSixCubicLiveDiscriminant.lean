module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Cubic profile slots with a repeated root -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveDiscriminant

/-- The derivative and root equations give the complete shifted
factorization, including when the two displayed slots coincide. -/
theorem cubic_double_factor {K : Type*} [CommRing K] (a b c d t x : K)
    (ht : a*t^3+b*t^2+c*t+d=0) (hd : 3*a*t^2+2*b*t+c=0) :
    a*x^3+b*x^2+c*x+d=(x-t)^2*(a*x+b+2*a*t) := by
  linear_combination ht+(x-t)*hd

/-- A real slot need not itself be the repeated root. -/
theorem repeated_cubic_slots {K : Type*} [Field K] (a b c d t x : K)
    (ht : a*t^3+b*t^2+c*t+d=0) (hd : 3*a*t^2+2*b*t+c=0)
    (hx : a*x^3+b*x^2+c*x+d=0) :
    x=t ∨ a*x+b+2*a*t=0 := by
  have hh : (x-t)^2*(a*x+b+2*a*t)=0 := by rw [← cubic_double_factor a b c d t x ht hd,hx]
  by_cases h : x=t
  · exact Or.inl h
  · exact Or.inr ((mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr h)))

end RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveDiscriminant
