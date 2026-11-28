module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Exact mass correction in a dense duplicated clock fiber -/
namespace RKResearch.Certified.Graded.OrderElevenLocalDense

/-- The apparent first-head substitution fails only by this exact
quadratic contribution at a doubled physical label. No division by
the total ordinary mass is involved. -/
theorem duplicate_weight_defect {R : Type*} [CommRing R] (b d h k U : R)
    (read : (b*h+d*k)*U=b*h^2+d*k^2) :
    (b*h+d*k)*((b+d)*U-(b*h+d*k))=b*d*(h-k)^2 := by
  linear_combination (b+d)*read

/-- Exact fixed rational quartic mass with the endpoint weight. -/
theorem jacobi_four_weighted_zero :
    (1/2-1/3:ℚ)-14*(1/3-1/4)+56*(1/4-1/5)-84*(1/5-1/6)+42*(1/6-1/7)=0 := by
  norm_num

/-- Exact fixed rational squared quartic mass. The coefficients are in
ascending degree and come from squaring `42 X^4−84 X^3+56 X^2−14 X+1`. -/
theorem jacobi_four_weighted_square :
    (1/2-1/3:ℚ)-28*(1/3-1/4)+308*(1/4-1/5)-1736*(1/5-1/6)+
      5572*(1/6-1/7)-10584*(1/7-1/8)+11760*(1/8-1/9)-
      7056*(1/9-1/10)+1764*(1/10-1/11)=1/330 := by
  norm_num

end RKResearch.Certified.Graded.OrderElevenLocalDense
