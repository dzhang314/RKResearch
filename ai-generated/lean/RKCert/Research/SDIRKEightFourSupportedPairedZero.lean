module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar receipts for the remaining paired physical zero thirds -/

namespace RKResearch.Certified.SDIRKEightFourSupportedPairedZero

theorem opposite_second_ratio {R : Type*} [CommRing R] (u : R) :
    (1+2*u-u^2)-(1+2*(-u)-(-u)^2)=4*u := by ring

theorem homogeneous_centered_pin {R : Type*} [CommRing R] {γ lam u : R}
    (h : γ*(lam+2)=1) :
    (2*γ*(1+2*u)-1)*(lam+2)=4*u-lam := by
  linear_combination 2*(1+2*u)*h

theorem literal_inner_pins :
    (164747 : ZMod 267613)*116942^2-83211^2=241314 ∧
    (2823 : ZMod 3517)*1514^2-1711^2=2937 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightFourSupportedPairedZero
