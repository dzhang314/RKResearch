module

public import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Fraction-free scalar compatibility of the three final live classes

The chronological support and the exact folded row budgets are earned
outside this scalar lemma. The third clock need not be assumed nonzero. -/

namespace RKResearch.Certified.Graded.NativeFinalThree

variable {K : Type*} [Field K] [CharZero K]

theorem clock_eq_first_or_second
    (s v P Q Z : K)
    (h0 : P + (3-2*s)*s*Q = v-1)
    (h1 : 2*(P+Q)-v*Z = -(3-2*s))
    (h2 : 3*(P+s*Q)-v^2*Z = -(3-2*s))
    (h3 : 4*(P+s^2*Q)-v^3*Z = -(3-2*s)-(s-1)*(v-1)) :
    v=1 ∨ v=s := by
  have hA : 2*(s-1)*(2*s*v-3*s-v)*Q = 2*(s-v)*(v-1) := by
    linear_combination -h2 + v*h1 + (3-2*v)*h0
  have hB : 2*(s-1)*(2*s*v^2-6*s-v^2)*Q = (s-v)*(v-1)*(2*v+3) := by
    linear_combination -h3 + v^2*h1 + (4-2*v^2)*h0
  have hprod : 3*(s-v)^2*(v-1)=0 := by
    linear_combination (2*s*v^2-6*s-v^2)*hA - (2*s*v-3*s-v)*hB
  by_cases hv : v=1
  · exact Or.inl hv
  · right
    have hmul : 3*(s-v)^2=0 := (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hv)
    have hsq : (s-v)^2=0 := (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    rw [pow_two] at hsq
    have he : s-v=0 := (mul_eq_zero.mp hsq).elim id id
    exact (sub_eq_zero.mp he).symm

end RKResearch.Certified.Graded.NativeFinalThree
