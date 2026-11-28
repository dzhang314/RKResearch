module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact arithmetic for the paired inverse-gap projection -/

namespace RKResearch.Certified.SDIRKEightTwoArithmeticThirds

theorem inverse_gap_sum {R : Type*} [CommRing R] (t z : R) :
    let w := t+z+3
    let F := (t+1)*(t+2)+(z+1)*(z+2)
    w^2-5*w+12-F=2*(1-t)*(1-z) := by
  dsimp
  ring

theorem common_fiber {K : Type*} [Field K] {F : K}
    (hF : F ≠ 0) (h : (8-F)*(F+2)=16) : F=6 := by
  have h' : F*(F-6)=0 := by linear_combination -h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hF)

theorem prime_support :
    (13^4*17*19*29*73^12*1193*43627^3 : ℕ) =
      606952555286871993045361344323680610272787567213 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightTwoArithmeticThirds
