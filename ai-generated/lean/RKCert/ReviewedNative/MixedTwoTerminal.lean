module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# The two-terminal mixed obstruction for a fully live top residual

These are the two primitive values for the residual profiles
`(X-a)(X-b)` and `X(X-a)(X-b)`. A site-only rule cannot recover both
by nonzero output coefficients confined to the two terminal sites.
-/
namespace RKResearch.Certified.MixedTwoTerminal

variable {K : Type*} [Field K] [CharZero K]

/-- Polynomial primitive at `x` of the monic two-terminal hull. -/
def prim0 (a b x : K) : K :=
  x^3/3-(a+b)*x^2/2+a*b*x

/-- Polynomial primitive at `x` of the hull with one extra clock mark. -/
def prim1 (a b x : K) : K :=
  x^4/4-(a+b)*x^3/3+a*b*x^2/2

theorem primitive_det (a b : K) :
    prim0 a b a*prim1 a b b - prim0 a b b*prim1 a b a =
      a^2*b^2*(a-b)^3/24 := by
  unfold prim0 prim1
  ring

theorem no_two_terminal_cancellation (a b u v : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hu : u ≠ 0)
    (h0 : u*prim0 a b a+v*prim0 a b b=0)
    (h1 : u*prim1 a b a+v*prim1 a b b=0) : False := by
  have h : u*(prim0 a b a*prim1 a b b - prim0 a b b*prim1 a b a)=0 := by
    linear_combination prim1 a b b*h0 - prim0 a b b*h1
  rw [primitive_det] at h
  exact (mul_ne_zero hu (div_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))
      (pow_ne_zero _ (sub_ne_zero.mpr hab))) (by norm_num))) h

#print axioms primitive_det
#print axioms no_two_terminal_cancellation

end RKResearch.Certified.MixedTwoTerminal
