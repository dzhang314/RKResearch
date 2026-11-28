module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Guarded arithmetic-to-inverse-gap scalars for the mixed phase -/

namespace RKResearch.Certified.SDIRKEightMixedArithmeticZeroThirds

theorem arithmetic_gap_factor {R : Type*} [CommRing R] {u r g : R}
    (h : (r+4*g^2)*(-2+u+4*u^2-u^3)=2*r*(3*u-2)) :
    r*(u-1)^2*(u-2)=4*g^2*(-2+u+4*u^2-u^3) := by
  linear_combination -h

theorem inverse_gap_coordinate {R : Type*} [CommRing R] {u t : R}
    (h : u*t=t+1) : u*(2*u-1)*t^2=(t+1)*(t+2) := by
  calc
    u*(2*u-1)*t^2 = 2*(u*t)^2-(u*t)*t := by ring
    _ = (t+1)*(t+2) := by rw [h]; ring

theorem characteristic_support :
    (13^6*37^3*9767*9883*156347*383099*231631013129*1423306149647 : ℕ) =
      466026778356356057041320539515986310698214453198038383 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightMixedArithmeticZeroThirds
