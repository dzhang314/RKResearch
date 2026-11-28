module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Undivided scalar gates in the zero-multiplier two-gap closure -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicZeroTwo

variable {K : Type*} [Field K]

/-- The first ghost fixes the relative cubic multiplier even if its
literal diagonal is zero. -/
theorem first_multiplier (z d r l₀ l₁ : K) (hr : r≠0)
    (h₀ : l₀*r=d^2) (h₁ : l₁*r=z*d^2) : l₁=z*l₀ := by
  have h : (l₁-z*l₀)*r=0 := by linear_combination h₁-z*h₀
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hr)

/-- At the second physical ghost the first tap cancels. -/
theorem second_diagonal_zero (w z g d : K) (hwz : w≠z) (hg : g≠0)
    (h : (w-z)*g*d^2=0) : d=0 := by
  by_contra hd
  exact (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hwz) hg) (pow_ne_zero 2 hd)) h

/-- The two-root relation works without dividing by a possibly
vanishing quadratic leader. -/
theorem two_root_sum (w z a b c : K) (hwz : w≠z)
    (hz : a*z^2+b*z+c=0) (hw : a*w^2+b*w+c=0) :
    a*(w+z)+b=0 := by
  have h : (w-z)*(a*(w+z)+b)=0 := by linear_combination hw-hz
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hwz)

theorem crossing_primitive {R : Type*} [CommRing R] (qz qw rz rw l : R)
    (hz : qz+l*rz=0) (hw : qw+l*rw=0) :
    qw*rz-qz*rw=0 := by
  linear_combination rz*hw-rw*hz

end RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicZeroTwo
