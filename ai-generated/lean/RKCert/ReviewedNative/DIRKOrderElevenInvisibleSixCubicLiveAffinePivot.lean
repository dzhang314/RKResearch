module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Undivided root selection in a fixed clock algebra -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveAffinePivot

variable {K : Type*} [Field K]

/-- The cofactor survives extension of the characteristic-zero
field; a unit leading read forces the selected root to be unique. -/
theorem unit_cofactor_unique (a b x y : K) (ha : a ≠ 0)
    (hx : a*x+b=0) (hy : a*y+b=0) : x=y := by
  have h : a*(x-y)=0 := by linear_combination hx-hy
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ha)

/-- The exactly known forbidden root determines the necessary
other root, without imposing a nonzero discriminant. -/
theorem quadratic_other_root (a b c x y : K) (hxy : x ≠ y)
    (hx : a*x^2+b*x+c=0) (hy : a*y^2+b*y+c=0) :
    a*(x+y)+b=0 := by
  have h : (x-y)*(a*(x+y)+b)=0 := by linear_combination hx-hy
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hxy)

/-- Distinguish two exactly named roots of a quadratic by
the evaluated affinity equation, without modular identities. -/
theorem two_roots_exhaust (a b c x y z : K) (ha : a ≠ 0)
    (hxy : x ≠ y) (hx : a*x^2+b*x+c=0) (hy : a*y^2+b*y+c=0)
    (hz : a*z^2+b*z+c=0) : z=x ∨ z=y := by
  have hs := quadratic_other_root a b c x y hxy hx hy
  have hp : a*((z-x)*(z-y))=0 := by
    linear_combination hz-hx-(z-x)*hs
  have ht := (mul_eq_zero.mp hp).resolve_left ha
  rcases mul_eq_zero.mp ht with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

end RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveAffinePivot
