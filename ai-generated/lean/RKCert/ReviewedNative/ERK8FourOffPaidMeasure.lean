module

public import RKCert.ReviewedNative.ERK8FourOffPaidNormalization

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Three-term clean barycentric measure, with every denominator cleared -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff.PaidProof ERK8PaidField
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped Classical

variable {K : Type*} [Field K]

theorem cleanSites_chart_eq (o : CleanOrientation) (u : K) :
    cleanSites (chartH o u) (chartX o u) (chartZ o u)=cleanSites u (midClock K) (1-u) := by
  ext a
  cases o <;> simp only [cleanSites,chartH,chartX,chartZ,Finset.mem_insert,Finset.mem_singleton] <;> tauto

theorem canonical_clean_clock_chart (o : CleanOrientation) (u : K)
    (D : CleanClocks (chartH o u) (chartX o u) (chartZ o u)) :
    CleanClocks u (midClock K) (1-u) := by
  cases o
  · exact D
  · exact ⟨D.h_ne_z,D.h_ne_x,D.x_ne_z.symm,D.root_h,D.root_z,D.root_x⟩
  · exact ⟨D.h_ne_x.symm,D.x_ne_z,D.h_ne_z,D.root_x,D.root_h,D.root_z⟩

theorem paid_canonical_cofactor_products [EightUnits K] {u c : K}
    (hq : sevenQuad u=0) (hc : 2*c=1) :
    14*(u-c)*(u-(1-u))=3 ∧ 14*((1-u)-c)*((1-u)-u)=3 ∧
      28*(c-u)*(c-(1-u))= -3 := by
  unfold sevenQuad at hq
  have ze : 2*c-1=0 := sub_eq_zero.mpr hc
  refine ⟨?_,?_,?_⟩
  · linear_combination 4*hq+(7-14*u)*ze
  · linear_combination 4*hq+(14*u-7)*ze
  · linear_combination -4*hq+7*(2*c-1)*ze

theorem paid_canonical_clean_cofactors [EightUnits K] {u c : K}
    (hq : sevenQuad u=0) (hc : 2*c=1) (D : CleanClocks u c (1-u)) :
    nodalCofactor (cleanSites u c (1-u)) u=(3/14:K)*u ∧
    nodalCofactor (cleanSites u c (1-u)) (1-u)=(3/14:K)*(1-u) ∧
    nodalCofactor (cleanSites u c (1-u)) c= -(3/28:K)*c := by
  obtain ⟨_,h₁,h₂,h₃⟩ := four_clean_cofactors D
  obtain ⟨a,b,m⟩ := paid_canonical_cofactor_products hq hc
  have n14 := fourteen_paid K
  have n28 : (28:K)≠0 := paidCastNe 28 (by decide)
  rw [h₁,h₂,h₃]
  refine ⟨?_,?_,?_⟩
  · apply mul_left_cancel₀ n14
    have h := mul_div_cancel₀ (3:K) n14
    linear_combination (norm := eight_ring K) u*a-u*h
  · apply mul_left_cancel₀ n14
    have h := mul_div_cancel₀ (3:K) n14
    linear_combination (norm := eight_ring K) (1-u)*b-(1-u)*h
  · apply mul_left_cancel₀ n28
    have h := mul_div_cancel₀ (3:K) n28
    linear_combination (norm := (field_simp [n28]; ring1)) c*m+c*h

def capFirst (o : CleanOrientation) (u : K) : K := (chartQuadratic o u).eval u
def capLast (o : CleanOrientation) (u : K) : K := (chartQuadratic o u).eval (1-u)
def capMiddle (o : CleanOrientation) (u : K) : K := (chartQuadratic o u).eval (midClock K)

def clearedMoment (o : CleanOrientation) (u : K) (n : ℕ) : K :=
  (2*u)^n*capLast o u*capMiddle o u+(2*(1-u))^n*capFirst o u*capMiddle o u-
    2*capFirst o u*capLast o u

theorem scaled_eval_match {P : K[X]} {o : CleanOrientation} {u kap : K}
    (S : ScaledPaidHead P o u kap) (d : P.natDegree≤2) (t : K) :
    P.eval t=(kap/chartScale o)*(chartQuadratic o u).eval t := by
  apply mul_left_cancel₀ S.scale_ne
  rw [S.eval d t,←mul_assoc,mul_div_cancel₀ _ S.scale_ne]

private theorem clean_term_quadratic [EightUnits K] {u a eta : K}
    (un : u≠0) (an : a≠0) (en : eta≠0) (n : ℕ) :
    u^(n+1)/(eta*a)/((3/14:K)*u)=(14/3:K)*(u^n/(eta*a)) := by
  rw [pow_succ]
  field_simp [un,an,en,three_paid K,fourteen_paid K]

private theorem clean_term_center [EightUnits K] {c a eta : K}
    (cn : c≠0) (an : a≠0) (en : eta≠0) (n : ℕ) :
    c^(n+1)/(eta*a)/(-(3/28:K)*c)= -(28/3:K)*(c^n/(eta*a)) := by
  rw [pow_succ]
  have d : (28:K)≠0 := paidCastNe 28 (by decide)
  field_simp [cn,an,en,three_paid K,d]

private theorem combine_three_cleared [EightUnits K] {c u v A B C eta : K}
    (hc : 2*c=1) (a : A≠0) (b : B≠0) (d : C≠0) (e : eta≠0) (n : ℕ) :
    (3*eta*A*B*C)*2^n*((14/3:K)*(u^n/(eta*A)) -(28/3:K)*(c^n/(eta*C))+
      (14/3:K)*(v^n/(eta*B))) =
      14*((2*u)^n*B*C+(2*v)^n*A*C-2*A*B) := by
  have m : (2:K)^n*c^n=1 := by rw [←mul_pow,hc,one_pow]
  have E :
      (3*eta*A*B*C)*2^n*((14/3:K)*(u^n/(eta*A)) -(28/3:K)*(c^n/(eta*C))+
        (14/3:K)*(v^n/(eta*B))) =
        14*(2^n*u^n*B*C+2^n*v^n*A*C-2*(2^n*c^n)*A*B) := by
    field_simp [a,b,d,e,three_paid K] <;> ring
  rw [E,m,show (2:K)*1=2 by ring,mul_pow,mul_pow]

/-- On the literal derived clean sites the only relevant nonconstant
cofactor factors are 3/14, -3/28, 3/14, after removing the clock itself. -/
theorem paid_cleared_moment [EightUnits K] {P : K[X]} {o : CleanOrientation} {u kap : K}
    (S : ScaledPaidHead P o u kap) (d : P.natDegree≤2)
    (hq : sevenQuad u=0) (D : CleanClocks (chartH o u) (chartX o u) (chartZ o u))
    (au : capFirst o u≠0) (bu : capLast o u≠0) (cu : capMiddle o u≠0) (n : ℕ) :
    (3*(kap/chartScale o)*capFirst o u*capLast o u*capMiddle o u)*2^n*
      nodalMeasure P (cleanSites (chartH o u) (chartX o u) (chartZ o u)) (X^(n+1)) =
        14*clearedMoment o u n := by
  let c := midClock K
  let v := 1-u
  let eta := kap/chartScale o
  have en : eta≠0 := div_ne_zero S.kap_ne S.scale_ne
  have hc : 2*c=1 := mul_div_cancel₀ (1:K) (two_paid K)
  have Dc := canonical_clean_clock_chart o u D
  change CleanClocks u c v at Dc
  obtain ⟨a,b,m⟩ := paid_canonical_clean_cofactors hq hc Dc
  have eqU : P.eval u=eta*capFirst o u := scaled_eval_match S d u
  have eqV : P.eval v=eta*capLast o u := scaled_eval_match S d v
  have eqC : P.eval c=eta*capMiddle o u := scaled_eval_match S d c
  rw [cleanSites_chart_eq,nodalMeasure_four P _ Dc,a,b,m]
  simp only [eval_pow,eval_X,zero_pow (Nat.succ_ne_zero n),zero_div,zero_add,eqU,eqV,eqC]
  rw [clean_term_quadratic (lobatto_clock_ne_zero Dc.root_h) au en,
    clean_term_center (lobatto_clock_ne_zero Dc.root_x) cu en,
    clean_term_quadratic (lobatto_clock_ne_zero Dc.root_z) bu en]
  simpa only [clearedMoment,eta,v,sub_eq_add_neg,neg_mul] using
    (combine_three_cleared (u:=u) (v:=v) hc au bu cu en n)

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.paid_cleared_moment
