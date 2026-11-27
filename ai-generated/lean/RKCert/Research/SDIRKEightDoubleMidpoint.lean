module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal scalar obstruction for a uniform midpoint triple at both ends -/

namespace RKResearch.Certified.SDIRKEightDoubleMidpoint

variable {K : Type*} [Field K] [CharZero K]

def spectral (m : K) : K := 18*m^2-126*m+203

theorem spectral_of_traces {m : K}
    (h : 6*m^2/7=6*(3-m)^2+4) : spectral m=0 := by
  unfold spectral
  linear_combination -(7/2 : K)*h

def newestResidualPivot (m : K) : K :=
  let b := 3-m
  let w := (1-m)^2
  let A := -16*b*(b^2-1)
  let B := 4*(3*m^4/35+3*b^4-12*b^2)
  let D := 2*b*(b^2-4)
  let E := 6*b
  let F := -4*(3*m^2/5+3*b^2-4)
  B*(D+E*w)-F*A*w

theorem pivot_linear {m : K} (hm : spectral m=0) :
    405*newestResidualPivot m=2274704*m-5703824 := by
  unfold newestResidualPivot spectral at *
  linear_combination
    (16*(1296*m^5-10044*m^4+30384*m^3-43056*m^2+33131*m+4081)/7)*hm

theorem pivot_ne_zero {m : K} (hm : spectral m=0) :
    newestResidualPivot m ≠ 0 := by
  intro hp
  have h := pivot_linear hm
  rw [hp, mul_zero] at h
  have hrat : m=(356489 : K)/142169 := by
    apply (eq_div_iff (by norm_num : (142169 : K) ≠ 0)).2
    linear_combination -(1/16 : K)*h
  rw [hrat] at hm
  norm_num [spectral] at hm

end RKResearch.Certified.SDIRKEightDoubleMidpoint
