module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Single-clock contrast recalibration
The coefficient profiles are evaluated at actual numerical clocks.
Only the coordinate of the genuine contrast at the calibration row is
assumed live. No ordinary weight at the other twin is inverted. -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleFive

variable {K I : Type*} [Field K]

/-- Reweighting a primitive row by one single-clock contrast removes
its whole contrast coefficient if it vanishes at the calibration row. -/
theorem calibrate_pure_row (B D H raw p : I → K) (j : I) (a w k l e : K)
    (live : B j≠0) (dj : D j=w*B j) (hj : H j=0)
    (single : ∀ i, B i≠0 → p i=p j)
    (hraw : ∀ i, raw i=a*B i+p i*D i+e*H i)
    (atj : raw j+l*B j-k*D j=0) (i : I) :
    raw i+l*B i-k*D i=(p i-k)*(D i-w*B i)+e*H i := by
  have bas := atj
  rw [hraw j, dj, hj] at bas
  have key : (a+l+(p j-k)*w)*B j=0 := by linear_combination bas
  have van := (mul_eq_zero.mp key).resolve_right live
  rw [hraw i]
  by_cases h : B i=0
  · rw [h]; ring
  · rw [single i h]
    linear_combination (B i)*van

end RKResearch.Certified.Graded.OrderElevenInvisibleFive
