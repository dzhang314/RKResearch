module

public import RKCert.ReviewedNative.ERK8FourOffPaidChart

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Denominator-cleared head normalization in the three paid charts -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff.PaidProof ERK8PaidField
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar

variable {K : Type*} [Field K]

private theorem normalize_leftCenterRight [EightUnits K] {P : K[X]} {u c theta kap : K}
    (h11 : (11:K)≠0) (hq : 7*u^2-7*u+1=0) (hc : 2*c-1=0) (pn : P≠0)
    (N : RawPaidShape P (u) (c) (1 - u) theta kap) :
    ScaledPaidHead P .leftCenterRight u kap := by
  have Ea : cleanE (u) (c) (1 - u)=2*(1-u) := by
    unfold cleanE
    linear_combination (3 - 5*u)*hc + (1)*hq
  have en : cleanE (u) (c) (1 - u)≠0 := by
    rw [Ea]
    refine mul_ne_zero (two_paid K) (sub_ne_zero.mpr ?_)
    intro n
    rw [←n] at hq
    exact (one_ne_zero : (1:K)≠0) (by linear_combination hq)
  have th : (14 - 56*u)*cleanE (u) (c) (1 - u)=28*cleanNumer (u) (c) := by
    unfold cleanE cleanNumer
    linear_combination (280*u^2 - 294*u + 42)*hc + (42 - 56*u)*hq
  have cof := raw_has_shape_coefficients N
  have n : kap≠0 := by
    intro k
    have z := N.ratio
    rw [k,zero_mul] at z
    have thz := (mul_eq_zero.mp z).resolve_right en
    exact pn (by rw [N.identity,thz,k]; simp)
  have T : 28*theta=kap*(14 - 56*u) := by
    apply mul_right_cancel₀ en
    linear_combination 28*N.ratio-kap*th
  have w0 : (14 - 56*u)*(c)*(1 - u)+28*2*(u)*(c)=(21*u + 3) := by
    linear_combination (28*u^2 - 7*u + 7)*hc + (4)*hq
  have w1 : -(14 - 56*u)*((c)+(1 - u))-28*(4*(c)+3*(u))=(-42*u - 69) := by
    linear_combination (28*u - 63)*hc + (-8)*hq
  have w2 : (14 - 56*u)+28*5=(154 - 56*u) := by ring
  refine ⟨chartScale_ne h11 _,n,?_,?_,?_⟩
  · rw [cof.c0]
    simp only [chartScale,chartQuadratic,shape]
    linear_combination (c)*(1 - u)*T+kap*w0
  · rw [cof.c1]
    simp only [chartScale,chartQuadratic,shape]
    linear_combination -((c)+(1 - u))*T+kap*w1
  · rw [cof.c2]
    simp only [chartScale,chartQuadratic,shape]
    linear_combination T+kap*w2

private theorem normalize_leftRightCenter [EightUnits K] {P : K[X]} {u c theta kap : K}
    (h11 : (11:K)≠0) (hq : 7*u^2-7*u+1=0) (hc : 2*c-1=0) (pn : P≠0)
    (N : RawPaidShape P (u) (1 - u) (c) theta kap) :
    ScaledPaidHead P .leftRightCenter u kap := by
  have Ea : cleanE (u) (1 - u) (c)=2*(1-u) := by
    unfold cleanE
    linear_combination (3 - 5*u)*hc + (1)*hq
  have en : cleanE (u) (1 - u) (c)≠0 := by
    rw [Ea]
    refine mul_ne_zero (two_paid K) (sub_ne_zero.mpr ?_)
    intro n
    rw [←n] at hq
    exact (one_ne_zero : (1:K)≠0) (by linear_combination hq)
  have th : (42 - 196*u)*cleanE (u) (1 - u) (c)=28*cleanNumer (u) (1 - u) := by
    unfold cleanE cleanNumer
    linear_combination (980*u^2 - 798*u + 126)*hc + (126 - 196*u)*hq
  have cof := raw_has_shape_coefficients N
  have n : kap≠0 := by
    intro k
    have z := N.ratio
    rw [k,zero_mul] at z
    have thz := (mul_eq_zero.mp z).resolve_right en
    exact pn (by rw [N.identity,thz,k]; simp)
  have T : 28*theta=kap*(42 - 196*u) := by
    apply mul_right_cancel₀ en
    linear_combination 28*N.ratio-kap*th
  have w0 : (42 - 196*u)*(1 - u)*(c)+28*2*(u)*(1 - u)=(15 - 21*u) := by
    linear_combination (98*u^2 - 119*u + 21)*hc + (6)*hq
  have w1 : -(42 - 196*u)*((1 - u)+(c))-28*(4*(1 - u)+3*(u))=(168*u - 147) := by
    linear_combination (98*u - 21)*hc + (-28)*hq
  have w2 : (42 - 196*u)+28*5=(182 - 196*u) := by ring
  refine ⟨chartScale_ne h11 _,n,?_,?_,?_⟩
  · rw [cof.c0]
    simp only [chartScale,chartQuadratic,shape]
    linear_combination (1 - u)*(c)*T+kap*w0
  · rw [cof.c1]
    simp only [chartScale,chartQuadratic,shape]
    linear_combination -((1 - u)+(c))*T+kap*w1
  · rw [cof.c2]
    simp only [chartScale,chartQuadratic,shape]
    linear_combination T+kap*w2

private theorem normalize_centerLeftRight [EightUnits K] {P : K[X]} {u c theta kap : K}
    (h11 : (11:K)≠0) (hq : 7*u^2-7*u+1=0) (hc : 2*c-1=0) (pn : P≠0)
    (N : RawPaidShape P (c) (u) (1 - u) theta kap) :
    ScaledPaidHead P .centerLeftRight u kap := by
  have Ea : 28*cleanE (c) (u) (1 - u)= -(11:K) := by
    unfold cleanE
    linear_combination (42*c - 35)*hc + (-24)*hq
  have en : cleanE (c) (u) (1 - u)≠0 := by
    intro e
    rw [e,mul_zero,eq_comm,neg_eq_zero] at Ea
    exact h11 Ea
  have th : (588 - 1568*u)*cleanE (c) (u) (1 - u)=308*cleanNumer (c) (u) := by
    unfold cleanE cleanNumer
    linear_combination (-2352*c*u + 1344*c + 1344*u - 504)*hc + (1344*u - 504)*hq
  have cof := raw_has_shape_coefficients N
  have n : kap≠0 := by
    intro k
    have z := N.ratio
    rw [k,zero_mul] at z
    have thz := (mul_eq_zero.mp z).resolve_right en
    exact pn (by rw [N.identity,thz,k]; simp)
  have T : 308*theta=kap*(588 - 1568*u) := by
    apply mul_right_cancel₀ en
    linear_combination 308*N.ratio-kap*th
  have w0 : (588 - 1568*u)*(u)*(1 - u)+308*2*(c)*(u)=(84*u + 84) := by
    linear_combination (308*u)*hc + (224*u - 84)*hq
  have w1 : -(588 - 1568*u)*((u)+(1 - u))-308*(4*(u)+3*(c))=(336*u - 1050) := by
    linear_combination (-462)*hc
  have w2 : (588 - 1568*u)+308*5=(2128 - 1568*u) := by ring
  refine ⟨chartScale_ne h11 _,n,?_,?_,?_⟩
  · rw [cof.c0]
    simp only [chartScale,chartQuadratic,shape]
    linear_combination (u)*(1 - u)*T+kap*w0
  · rw [cof.c1]
    simp only [chartScale,chartQuadratic,shape]
    linear_combination -((u)+(1 - u))*T+kap*w1
  · rw [cof.c2]
    simp only [chartScale,chartQuadratic,shape]
    linear_combination T+kap*w2

theorem scaled_actual_head_outside11 [EightUnits K] {P : K[X]} {o : CleanOrientation}
    {u theta kap : K} (h11 : (11:K)≠0) (hq : sevenQuad u=0) (pn : P≠0)
    (N : RawPaidShape P (chartH o u) (chartX o u) (chartZ o u) theta kap) :
    ScaledPaidHead P o u kap := by
  have hc : 2*midClock K-1=0 := by
    rw [mul_div_cancel₀ _ (two_paid K),sub_self]
  rcases o with _|_|_
  · exact normalize_leftCenterRight h11 hq hc pn N
  · exact normalize_leftRightCenter h11 hq hc pn N
  · exact normalize_centerLeftRight h11 hq hc pn N

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.scaled_actual_head_outside11
