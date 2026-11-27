module

public import RKCert.ReviewedNative.ERK149SevenClockPrefix

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKResearch.Certified.ERK149SevenClockOrderTen

open RKResearch RKResearch.FiniteRootedTree
open RKResearch.Certified.ERK149SevenClockPrefix (residual shape₀ shape₁)
open scoped FiniteRootedTree

def leaf' : FiniteRootedTree := .leaf

def source0 : FiniteRootedTree :=
  (((((leaf' ◂ leaf') ◂ leaf') ◂ leaf') ◂ leaf') ◂ leaf') ◂ leaf'

def source1 : FiniteRootedTree :=
  (((leaf' ◂ leaf') ◂ leaf') ◂ leaf') ◂ ((leaf' ◂ leaf') ◂ leaf')

def source2 : FiniteRootedTree :=
  ((leaf' ◂ leaf') ◂ leaf') ◂ (((leaf' ◂ leaf') ◂ leaf') ◂ leaf')

def shapeX : Fin 7 → ℚ := ![0,0,1/2,-(3/2),1,0,0]

/-- Two genuinely direct size-seven rooted source combinations. No
root child in any source uses more than five vertices. -/
theorem directSourceD (j : Fin 7) :
    -9 * residual source0 j + (27/2) * residual source1 j +
      18 * residual source2 j = shape₀ j := by
  fin_cases j <;> decide +kernel

theorem directSourceXD (j : Fin 7) :
    (9/2) * residual source0 j + (27/4) * residual source1 j -
      27 * residual source2 j = shapeX j := by
  fin_cases j <;> decide +kernel

def six0 : FiniteRootedTree :=
  ((((leaf' ◂ leaf') ◂ leaf') ◂ leaf') ◂ leaf') ◂ leaf'

def six1 : FiniteRootedTree :=
  ((leaf' ◂ leaf') ◂ leaf') ◂ ((leaf' ◂ leaf') ◂ leaf')

theorem sizeSixSourceD (j : Fin 7) :
    -9 * residual six0 j + 27 * residual six1 j = shape₀ j := by
  fin_cases j <;> decide +kernel

theorem sizeSixSourceDQ (j : Fin 7) :
    3 * residual six0 j - 6 * residual six1 j = shape₁ j := by
  fin_cases j <;> decide +kernel

variable {K : Type*} [Field K]

/-- A three-site reverse rule killing the three paid scalar powers
cannot leave a nonzero charge at even its first, distinguished site. -/
theorem firstCharge_zero (a b c u v w : K) (hab : a ≠ b) (hac : a ≠ c)
    (h₀ : u+v+w=0)
    (h₁ : a*u+b*v+c*w=0)
    (h₂ : a^2*u+b^2*v+c^2*w=0) :
    u=0 := by
  have h : u*((a-b)*(a-c))=0 := by
    linear_combination h₂ - (b+c)*h₁ + b*c*h₀
  exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac))

/-- The movable split is absorbed in the weighted output whenever the
new decoder differs from its old copy by exactly one defect letter. -/
theorem split_gauge (s W a r : K) (hs : s ≠ 0) :
    s * (a + r/s) + (W-s)*a = W*a+r := by
  field_simp
  ring

end RKResearch.Certified.ERK149SevenClockOrderTen
