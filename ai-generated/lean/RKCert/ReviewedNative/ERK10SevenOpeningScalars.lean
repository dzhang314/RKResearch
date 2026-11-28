module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

public section

namespace RKResearch.Certified.ERK10SevenOpeningScalars

/-- The fourth (size-five) equation tests the stage-5 clock without dividing
by the determinant of the first three equations. These are scalar consequences
of the two-dimensional projected defect chart, not assumptions on all ERK. -/
theorem fifth_clock
    (r s T U J : ℚ) (r0 : r ≠ 0) (r1 : r ≠ 1) (r32 : 2*r ≠ 3)
    (h1 : T+U+r*J=s^2/2)
    (h2 : (2/3)*T+U+r^2*J=s^3/3)
    (h3 : (3-2*r)*(U+r^2*(3-2*r)*J)=2*(s-1)*T)
    (h4 : (3-2*r)*(U+r^3*J-s^4/4)+(3-2*r+(r-1)*(s-1))*T/2=0) :
    s=0 ∨ s=1 ∨ s=r := by
  have hh :
      r*s^2*(r-1)*(r-s)^2*(2*r-3)*(s-1)/2=0 := by
    linear_combination
      (r^2*(r-1)*(2*r-3)*(r*s+r-3*s))*h1 -
      (r*(r-1)*(2*r-3)*(2*r^2*s+6*r^2-7*r*s-3*r-3*s)/2)*h2 -
      (r*(r-1)*(4*r^2-3*r*s-5*r+3*s)/6)*h3 -
      (2*r*(r-1)*(2*r^2-r-3*s)/3)*h4
  have hs := (div_eq_zero_iff.mp hh).resolve_right (by decide)
  by_cases a : s=0
  · exact Or.inl a
  by_cases b : s=1
  · exact Or.inr (Or.inl b)
  by_cases c : s=r
  · exact Or.inr (Or.inr c)
  exfalso
  apply (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero r0 (pow_ne_zero _ a)) (sub_ne_zero.mpr r1))
    (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm c)))) (sub_ne_zero.mpr r32))
    (sub_ne_zero.mpr b))
  exact hs

/-- The isolated projected reverse degree-five moment and the two scalar
quadrature coefficients are incompatible at a nonzero rational horizon. -/
theorem weighted_last_clock_impossible
    (z t w1 wt : ℚ) (z0 : z ≠ 0) (t1 : t ≠ 1)
    (hn : 15*t*(z-2)^2=z*(12*z^2-45*z+40))
    (h1 : 12*(t-1)*w1=z^2*(-4*t*z+12*t+3*z^2-8*z))
    (ht : 4*t*(t-2)*(t-1)*wt=z^2*(z-2)^2)
    (hw : w1+t^2*(t-2)^2*wt=0) : False := by
  have hh : (t-1)*(z^2*(3*t*(z-2)^2-3*z^2+8*z))=0 := by
    linear_combination (12*(t-1))*hw-h1-(3*t*(t-2))*ht
  have hg := (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr t1))).resolve_left (pow_ne_zero _ z0)
  have hz : z*(3*z^2-15*z+20)=0 := by
    linear_combination (5/4)*hg-(1/4)*hn
  have hq := (mul_eq_zero.mp hz).resolve_left z0
  nlinarith [sq_nonneg (z-5/2)]

/-- The anchored three-node degree-four quadrature requires a square root of 6
in the scalar field; this is the denominator-free arithmetic implication. -/
theorem anchored_three_clock_square
    (a b : ℚ) (h0 : 1/4-(a+b)/3+a*b/2=0) (h1 : 1/5-(a+b)/4+a*b/3=0) :
    (5*(a-b))^2=6 := by
  have hS : a+b=6/5 := by linear_combination 24*h0-36*h1
  have hp : a*b=3/10 := by linear_combination 18*h0-24*h1
  linear_combination (25*(a+b+6/5))*hS-100*hp

end RKResearch.Certified.ERK10SevenOpeningScalars

#print axioms RKResearch.Certified.ERK10SevenOpeningScalars.fifth_clock
#print axioms RKResearch.Certified.ERK10SevenOpeningScalars.weighted_last_clock_impossible
#print axioms RKResearch.Certified.ERK10SevenOpeningScalars.anchored_three_clock_square
