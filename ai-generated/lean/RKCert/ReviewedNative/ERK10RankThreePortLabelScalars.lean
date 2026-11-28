module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

namespace RKResearch.Certified.ERK10RankThreePortLabelScalars

theorem weighted_quadratic
    (a b c : ℚ) (m1 : a/4+b/3+c/2=0) (m2 : a/5+b/4+c/3=0) :
    b=-(6/5)*a ∧ c=(3/10)*a := by
  constructor
  · linear_combination -24*m1+36*m2
  · linear_combination 18*m1-24*m2

theorem primitive_remainder (x : ℚ) :
    x^4/4-(2/5)*x^3+(3/20)*x^2 =
      (x^2-(6/5)*x+3/10)*(x^2/4-x/10-9/200)+27/2000-(3/125)*x := by
  ring

theorem primitive_not_quadratic_multiple (r0 r1 r2 : ℚ)
    (hall : ∀ x : ℚ, x^4/4-(2/5)*x^3+(3/20)*x^2 =
        (x^2-(6/5)*x+3/10)*(r2*x^2+r1*x+r0)) :
    False := by
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall (-1)
  have h3 := hall 2
  norm_num at h0 h1 h2 h3
  linarith

end RKResearch.Certified.ERK10RankThreePortLabelScalars

#print axioms RKResearch.Certified.ERK10RankThreePortLabelScalars.weighted_quadratic
#print axioms RKResearch.Certified.ERK10RankThreePortLabelScalars.primitive_remainder
#print axioms RKResearch.Certified.ERK10RankThreePortLabelScalars.primitive_not_quadratic_multiple
