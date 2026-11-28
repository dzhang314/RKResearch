module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ArithmeticLiteralStageExchange

/-- Unlike the star front, the arithmetic front cannot exchange the
literal second and third as triangular rows. The normalized strict
third-to-second coupling has nonzero quadratic norm in characteristic
zero. -/
theorem arithmeticLiteralCouplingNorm {R : Type*} [CommRing R]
    (t : R) (ht : 2*t^2=1) : (1+6*t)*(1-6*t)=-17 := by
  linear_combination -18*ht

theorem arithmeticLiteralCouplingNonzero {R : Type*} [Field R] [CharZero R]
    (t : R) (ht : 2*t^2=1) : (1:R)/2+3*t ≠ 0 := by
  intro hm
  have hh : 1+6*t=0 := by
    linear_combination 2*hm
  have hr := arithmeticLiteralCouplingNorm t ht
  rw [hh,zero_mul] at hr
  norm_num at hr

#print axioms arithmeticLiteralCouplingNorm
#print axioms arithmeticLiteralCouplingNonzero

end RKCert.ReviewedNative.SDIRK8ArithmeticLiteralStageExchange
