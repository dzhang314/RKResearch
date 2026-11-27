module

public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Algebra.Field.Defs

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK10CanonicalCubicRankGate

variable {K : Type*} [Field K] [CharZero K]

theorem lower_donor_minor (p q : K) (hp : p ≠ 0) :
    (-p^4/36)*(3*q^2*(3*p-2*q)/(4*p^2)) -
      (5*p*q^3/9-p^2*q^2/3-q^4/4)*(3*p/4) =
      3*p*q^2*(p-q)^2/16 := by
  field_simp [hp]
  ring

/-- The first two nonconstant primitive moments, for an anchored input. -/
def j₀ (r x : K) : K := x^3/3-r*x^2/2
def j₁ (r x : K) : K := x^4/4-r*x^3/3

theorem point_first_high_minor (a r : K) :
    j₀ r a * j₁ r r - j₁ r a * j₀ r r = a^2*r^3*(a-r)^2/24 := by
  unfold j₀ j₁
  ring

theorem point_first_high (a r μ : K) (hr : r ≠ 0)
    (h₀ : j₀ r a = μ*j₀ r r) (h₁ : j₁ r a = μ*j₁ r r) :
    a = 0 ∨ a = r := by
  by_cases ha : a=0
  · exact Or.inl ha
  right
  by_contra har
  have hz : a^2*r^3*(a-r)^2/24=0 := by
    rw [← point_first_high_minor,h₀,h₁]
    ring
  exact (div_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 3 hr))
      (pow_ne_zero 2 (sub_ne_zero.mpr har))) (by norm_num)) hz

def det3 (a b c d e f g h i : K) : K :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

theorem generic_second_high_minor (a b : K) :
    det3 (a^2/2) (a^3/3) (a^4/4) a (a^2) (a^3)
      (b^2/2) (b^3/3) (b^4/4) = a^4*b^2*(a-b)^2/24 := by
  unfold det3
  ring

theorem generic_second_high (a b u v : K) (ha : a ≠ 0)
    (h₂ : b^2/2 = u*(a^2/2)+v*a)
    (h₃ : b^3/3 = u*(a^3/3)+v*a^2)
    (h₄ : b^4/4 = u*(a^4/4)+v*a^3) :
    b=0 ∨ b=a := by
  by_cases hb : b=0
  · exact Or.inl hb
  right
  by_contra hba
  have hz : a^4*b^2*(a-b)^2/24=0 := by
    rw [← generic_second_high_minor,h₂,h₃,h₄]
    unfold det3
    ring
  exact (div_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 ha) (pow_ne_zero 2 hb))
      (pow_ne_zero 2 (sub_ne_zero.mpr (fun h => hba h.symm)))) (by norm_num)) hz

theorem old_clock_eval_not_primitive (a : K) :
    (a^2/2)*a^2-(a^3/3)*a=a^4/6 := by ring

theorem same_clock_tap_zero (a v μ : K) (ha : a ≠ 0)
    (h₁ : v*a = μ*(a^2/2)) (h₂ : v*a^2 = μ*(a^3/3)) :
    v=0 := by
  have hz : v*a^4=0 := by linear_combination -2*a^3*h₁+3*a^2*h₂
  exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero 4 ha)

end RKResearch.Certified.ERK10CanonicalCubicRankGate
