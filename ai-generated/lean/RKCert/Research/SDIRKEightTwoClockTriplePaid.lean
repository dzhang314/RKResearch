module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar receipts for the paid strict SDIRK8 two-clock, three-zero exclusion -/

namespace RKResearch.Certified.SDIRKEightTwoClockTriplePaid

theorem gauss_pair_difference {R : Type*} [CommRing R] (a b : R) :
    (70*b^4-140*b^3+90*b^2-20*b+1) -
      (70*a^4-140*a^3+90*a^2-20*a+1) =
    (b-a)*(b+a-1)*(70*(b*b-b+a*a-a)+20) := by
  ring

theorem mirror_primitive_reversal {R : Type*} [CommRing R] {a b f t : R}
    (h : a+b=1) :
    (f-t)-b*f = -(t-a*f) := by
  linear_combination -f*h

theorem mirror_singleton_cleared {R : Type*} [CommRing R] {a q : R}
    (h : 7*q=7*a^2-7*a+2) :
    7*(-a^4+2*a^3-6*a^2*q) = -(a^2*(7*a-2)*(7*a-6)) := by
  linear_combination (-6*a^2)*h

def tripleClockSingletonGate {R : Type*} [CommRing R] (a : R) : R :=
  a^2*(7*a-2)*(7*a-6)

theorem singleton_five_survivors :
    tripleClockSingletonGate (137 : ZMod 139) ≠ 0 ∧
    tripleClockSingletonGate (302 : ZMod 509) ≠ 0 ∧
    tripleClockSingletonGate (412 : ZMod 739) ≠ 0 ∧
    tripleClockSingletonGate (42484 : ZMod 1352963) ≠ 0 ∧
    tripleClockSingletonGate (3244963624905 : ZMod 3716728837183) ≠ 0 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightTwoClockTriplePaid
