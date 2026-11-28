module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Scalar gate for a repeated receiver clock
The valid moment reads use a common numerical donor set after grouping
literal taps, not a reordered or merged tableau. -/
namespace RKResearch.Certified.Graded.OrderElevenLocalDuplicate

variable {K : Type*} [Field K]

/-- The common affine read fixes the same marked amplitude on two
physical receivers at the same numerical clock. -/
theorem same_amplitude (base slope target head x y : K)
    (guard : slope-head≠0)
    (hx : base+slope*x=target+head*x)
    (hy : base+slope*y=target+head*y) : x=y := by
  have z : (slope-head)*(x-y)=0 := by linear_combination hx-hy
  exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left guard)

/-- Two distinct live head values cannot share a vanishing linear
weighted read and a vanishing quadratic weighted read. -/
theorem two_head_square_nonzero (p q a b : K)
    (hp : p≠0) (ha : a≠0) (hab : a≠b)
    (h : p*a+q*b=0) : p*a^2+q*b^2≠0 := by
  intro h2
  have z : (p*a)*(a-b)=0 := by linear_combination h2-b*h
  exact (mul_ne_zero (mul_ne_zero hp ha) (sub_ne_zero.mpr hab)) z

end RKResearch.Certified.Graded.OrderElevenLocalDuplicate
