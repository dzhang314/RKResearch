module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ClockTwinReceipts

/-- A degree-zero and degree-one weighted observation separate two distinct
exceptions to a cubic profile, provided each exception has nonzero weight
and cubic defect. -/
theorem twoReceiverAgreement {K : Type*} [Field K] (a b wa wb ha hb pa pb : K)
    (hClock : a≠b) (hwA : wa≠0) (hwB : wb≠0) (hhA : ha≠0) (hhB : hb≠0)
    (h0 : wa*ha*(ha-pa) + wb*hb*(hb-pb)=0)
    (h1 : a*wa*ha*(ha-pa) + b*wb*hb*(hb-pb)=0) :
    ha=pa ∧ hb=pb := by
  have hA : ((b-a)*(wa*ha))*(ha-pa)=0 := by linear_combination b*h0-h1
  have hB : ((a-b)*(wb*hb))*(hb-pb)=0 := by linear_combination a*h0-h1
  constructor
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hA).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr hClock.symm) (mul_ne_zero hwA hhA)))
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hB).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr hClock) (mul_ne_zero hwB hhB)))

/-- The four ordinary integration probes of a cubic are nonsingular in
characteristic zero; no positivity or ordering is used. -/
theorem cubicHilbert {K : Type*} [Field K] [CharZero K] (a b c d : K)
    (h0 : a+b/2+c/3+d/4=0)
    (h1 : a/2+b/3+c/4+d/5=0)
    (h2 : a/3+b/4+c/5+d/6=0)
    (h3 : a/4+b/5+c/6+d/7=0) :
    a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  constructor
  · linear_combination 16*h0-120*h1+240*h2-140*h3
  constructor
  · linear_combination -120*h0+1200*h1-2700*h2+1680*h3
  constructor
  · linear_combination 240*h0-2700*h1+6480*h2-4200*h3
  · linear_combination -140*h0+1680*h1-4200*h2+2800*h3

end RKCert.ReviewedNative.SDIRK8ClockTwinReceipts
