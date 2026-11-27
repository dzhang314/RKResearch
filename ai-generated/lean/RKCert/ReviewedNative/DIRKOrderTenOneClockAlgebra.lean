module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Exact field algebra in the one-dirty-clock DIRK10 reduction

The companion note derives these equations from the paid native flags and
from the actual inclusive physical prefix. This file does not posit a
clock mask that is not already carried by the tableau. -/
namespace RKResearch.Certified.Graded.OneClockAlgebra

variable {K : Type*} [Field K]

/-- First genuinely exterior row: the two retained elementary moments
fix the total tap from the old nonzero clock. The diagonal is not dropped. -/
theorem first_exterior_tap (ξ y S d : K) (pay : (6 : K) ≠ 0)
    (one : S*ξ + d*y = y^2/2) (two : S*ξ^2 + d*y^2 = y^3/3) :
    6*ξ*(y-ξ)*S = y^3 := by
  have two_ne : (2 : K) ≠ 0 := by intro h; apply pay; linear_combination 3*h
  have three_ne : (3 : K) ≠ 0 := by intro h; apply pay; linear_combination 2*h
  have u : 2*(S*ξ + d*y)=y^2 := by rw [one]; field_simp
  have v : 3*(S*ξ^2 + d*y^2)=y^3 := by rw [two]; field_simp
  linear_combination 3*y*u - 2*v

/-- The simple second exterior cut: three double roots cannot fit the two
endpoint-inclusive primitives. This is division-free after multiplying out. -/
theorem no_zero_head_second (a x : K) (x0 : x ≠ 0)
    (m0 : x^3*(2*a-x)=0) (m1 : x^4*(5*a-3*x)=0) : False := by
  have u := (mul_eq_zero.mp m0).resolve_left (pow_ne_zero _ x0)
  have v := (mul_eq_zero.mp m1).resolve_left (pow_ne_zero _ x0)
  apply x0
  linear_combination 5*u - 2*v

/-- The finite-pair cubic extracted from the paid rank-one paired cut. -/
theorem paired_cut_cubic (a b u : K)
    (eq : b*(2*a-b)*(a-u) + a*(2*b-a)*(b-u) = 0) :
    u*(4*a*b-a^2-b^2)-a*b*(a+b)=0 := by
  linear_combination -eq

/-- A degree-two head coefficient with three distinct zeros vanishes.
No order, roots in an extension, or decidable equality is assumed. -/
theorem quadratic_three_zeros (a b c u v w : K)
    (ab : b ≠ a) (ac : c ≠ a) (bc : c ≠ b)
    (ha : u+v*a+w*a^2=0) (hb : u+v*b+w*b^2=0) (hc : u+v*c+w*c^2=0) :
    u=0 ∧ v=0 ∧ w=0 := by
  have vb : (b-a)*(v+w*(a+b))=0 := by linear_combination hb-ha
  have vc : (c-a)*(v+w*(a+c))=0 := by linear_combination hc-ha
  have vb' := (mul_eq_zero.mp vb).resolve_left (sub_ne_zero.mpr ab)
  have vc' := (mul_eq_zero.mp vc).resolve_left (sub_ne_zero.mpr ac)
  have wc : w*(c-b)=0 := by linear_combination vc'-vb'
  have wz := (mul_eq_zero.mp wc).resolve_right (sub_ne_zero.mpr bc)
  have vz : v=0 := by simpa [wz] using vb'
  exact ⟨by simpa [wz,vz] using ha,vz,wz⟩

/-- On exactly two exterior head labels, their quadratic coefficient is
nonzero at any other label, unless the coefficient is identically zero. -/
theorem quadratic_core_nonzero (a b ξ u v w : K)
    (ab : b ≠ a) (ax : ξ ≠ a) (bx : ξ ≠ b)
    (ha : u+v*a+w*a^2=0) (hb : u+v*b+w*b^2=0)
    (nz : ¬ (u=0 ∧ v=0 ∧ w=0)) : u+v*ξ+w*ξ^2≠0 := by
  intro hc
  exact nz (quadratic_three_zeros a b ξ u v w ab ax bx ha hb hc)

/-- Paid degree-five quadrature in an inclusive prefix with exactly two
earlier nonzero donor clocks. Their sum/product are the anchored Jacobi pair. -/
theorem inclusive_five_two_donors (a b x : K) (x0 : x ≠ 0)
    (m0 : x^3*(10*a*b-5*(a+b)*x+3*x^2)=0)
    (m1 : x^4*(5*a*b-3*(a+b)*x+2*x^2)=0) :
    a+b=x ∧ 5*a*b=x^2 := by
  have u := (mul_eq_zero.mp m0).resolve_left (pow_ne_zero _ x0)
  have v := (mul_eq_zero.mp m1).resolve_left (pow_ne_zero _ x0)
  have s : x*(a+b-x)=0 := by linear_combination u-2*v
  have s' := (mul_eq_zero.mp s).resolve_left x0
  exact ⟨sub_eq_zero.mp s', by linear_combination v+3*x*s'⟩

end RKResearch.Certified.Graded.OneClockAlgebra
