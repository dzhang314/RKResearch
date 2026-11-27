module

public import RKCert.ReviewedNative.ERK149TwoPairChronology

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK149TwoPairAnchored

open ERK149TwoPairChronology

variable {K : Type*} [Field K] [CharZero K]

theorem first_cubics (a b : K) :
    G a b a = a^3*(a-2*b)/12 ∧ G a b b = b^3*(b-2*a)/12 := by
  constructor <;> unfold G <;> ring

omit [CharZero K] in
theorem paired_moments (a b u v : K) (hab : a ≠ b)
    (h₀ : u+v=0) (h₁ : a*u+b*v=0) : u = 0 := by
  have z : (a-b)*u=0 := by linear_combination h₁-b*h₀
  exact (mul_eq_zero.mp z).resolve_left (sub_ne_zero.mpr hab)

theorem first_tap_resonance (b : K) (hb : b ≠ 0) :
    (2*b)*(3*b-2*(2*b))/(6*(b-2*b)) = b/3 := by
  have hn : b-2*b ≠ 0 := by
    rw [show b-2*b = -b by ring]
    exact neg_ne_zero.mpr hb
  field_simp
  ring

/-- The final contradictory pooled response in the first-pair anchor
case. The inputs x,y are the two honest products of physical taps. -/
theorem first_pair_anchor_residual (a x y : K) (ha : a ≠ 0)
    (hh : -a^2*x/2-a^4/3=0)
    (hu : -(4*a/3)*a^2/2+a*x+2*a*y=0) :
    -(4*a/3)*a^3/3+a^2*x+(2*a)^2*y+(a/3)*(-2*a^3/3) = 4*a^4/3 := by
  have hx₀ : a^2*(x+2*a^2/3)=0 := by linear_combination -2*hh
  have hx : x = -2*a^2/3 := by
    have he := (mul_eq_zero.mp hx₀).resolve_left (pow_ne_zero 2 ha)
    linear_combination he
  have hy₀ : (2*a)*(y-2*a^2/3)=0 := by linear_combination hu-a*hx
  have hy : y=2*a^2/3 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hy₀).resolve_left (mul_ne_zero (by norm_num) ha))
  rw [hx,hy]
  ring

end RKResearch.Certified.ERK149TwoPairAnchored
