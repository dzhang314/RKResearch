module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The two scalar elimination gates used in the normalized DIRK11 chronology.
The deduction of their hypotheses from rooted order and chronologies is separate. -/

namespace RKCert.ReviewedNative.DIRK11DirtyChronologyScalarGates

theorem midpoint {K : Type*} [Field K] {u v e f : K} (huv : u ≠ v)
    (h : (u-e)*(2*(1-v)-(1-f)) = (v-e)*(2*(1-u)-(1-f))) :
    2*e = 1+f := by
  have hprod : (v-u)*(2*e-(1+f)) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr huv.symm))

def p4 {K : Type*} [Ring K] (x : K) : K :=
  42*x^4 - 84*x^3 + 56*x^2 - 14*x + 1

def p5 {K : Type*} [Ring K] (x : K) : K :=
  (2*x-1)*(66*x^4 - 132*x^3 + 84*x^2 - 18*x + 1)

def tailPoly {K : Type*} [Ring K] (x : K) : K :=
  1386*x^8 - 2772*x^7 + 1092*x^6 + 1134*x^5 - 1077*x^4 +
    252*x^3 + 22*x^2 - 14*x + 1

theorem pencilCross {K : Type*} [Field K] [CharZero K] (f : K) :
    8 * (p4 f * p5 ((1+f)/2) - p5 f * p4 ((1+f)/2)) =
      (1-f) * tailPoly f := by
  unfold p4 p5 tailPoly
  ring

theorem pencilRoot {K : Type*} [Field K] [CharZero K] {f a : K} (hf : f ≠ 1)
    (h₁ : p5 f + a*p4 f = 0)
    (h₂ : p5 ((1+f)/2) + a*p4 ((1+f)/2) = 0) :
    tailPoly f = 0 := by
  have hd : p4 f * p5 ((1+f)/2) - p5 f * p4 ((1+f)/2) = 0 := by
    linear_combination p4 f * h₂ - p4 ((1+f)/2) * h₁
  have hprod := (pencilCross f).symm
  rw [hd, mul_zero] at hprod
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hf.symm)

end RKCert.ReviewedNative.DIRK11DirtyChronologyScalarGates

#print axioms RKCert.ReviewedNative.DIRK11DirtyChronologyScalarGates.midpoint
#print axioms RKCert.ReviewedNative.DIRK11DirtyChronologyScalarGates.pencilRoot
