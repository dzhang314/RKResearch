module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paid scalar gates for the distinct-three-zero low-support branches -/

namespace RKResearch.Certified.SDIRKEightThreeZeroLowSupport

theorem arithmetic_zero_factor {R : Type*} [CommRing R] (u : R) :
    (1+4*u-4*u^2)*(-2+u+4*u^2-u^3)+4*u^2*(3*u-2)=
      -(1+2*u-u^2)*(4*u^3-12*u^2+3*u+2) := by
  ring

theorem repeated_clock_slope {K : Type*} [Field K]
    {F G g₁ g₂ : K} (he : g₁ ≠ g₂) (h₁ : F+G*g₁=0) (h₂ : F+G*g₂=0) :
    G=0 := by
  have h : G*(g₁-g₂)=0 := by linear_combination h₁-h₂
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr he)

theorem zero_forward_3517 :
    (1+4*338-4*338^2 : ZMod 3517)*(-2+338+4*338^2-338^3)+
      4*338^2*(3*338-2)=0 ∧
    (-2+338+4*338^2-338^3 : ZMod 3517)≠0 := by decide +kernel

end RKResearch.Certified.SDIRKEightThreeZeroLowSupport
