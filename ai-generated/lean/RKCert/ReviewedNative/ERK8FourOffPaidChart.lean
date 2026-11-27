module

public import RKCert.ReviewedNative.ERK8FourOffPaidQuadraticClosure
public import RKCert.ReviewedNative.ERK8PaidArithmetic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Three exhaustive clean-clock orientations outside characteristic eleven -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff.PaidProof OneOff ERKTaggedHorizon ERK8PaidField
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped Classical

variable {K : Type*} [Field K]

inductive CleanOrientation
  | leftCenterRight
  | leftRightCenter
  | centerLeftRight
  deriving DecidableEq

abbrev midClock (K : Type*) [Field K] := (1:K)/2

def chartH (o : CleanOrientation) (u : K) : K :=
  match o with
  | .leftCenterRight => u
  | .leftRightCenter => u
  | .centerLeftRight => midClock K

def chartX (o : CleanOrientation) (u : K) : K :=
  match o with
  | .leftCenterRight => midClock K
  | .leftRightCenter => 1-u
  | .centerLeftRight => u

def chartZ (o : CleanOrientation) (u : K) : K :=
  match o with
  | .leftCenterRight => 1-u
  | .leftRightCenter => midClock K
  | .centerLeftRight => 1-u

def sevenQuad (u : K) : K := 7*u^2-7*u+1

theorem paid_clean_orientation [EightUnits K] {h x z : K}
    (D : CleanClocks h x z) :
    ∃ (o : CleanOrientation) (u : K), sevenQuad u=0 ∧
      h=chartH o u ∧ x=chartX o u ∧ z=chartZ o u := by
  have split {t : K} (ht : lobattoNumer t=0) : t=midClock K ∨ sevenQuad t=0 := by
    rcases mul_eq_zero.mp ht with half|q
    · left
      apply (eq_div_iff (two_paid K)).mpr
      linear_combination half
    · exact Or.inr q
  have comp {u v : K} (u0 : sevenQuad u=0) (v0 : sevenQuad v=0) (uv : u≠v) : v=1-u := by
    unfold sevenQuad at u0 v0
    have e : 7*(u-v)*(u+v-1)=0 := by linear_combination u0-v0
    have q := (mul_eq_zero.mp e).resolve_left (mul_ne_zero (seven_paid K) (sub_ne_zero.mpr uv))
    linear_combination q
  rcases split D.root_h with hm|hq
  · have xq := (split D.root_x).resolve_left (fun r=>D.h_ne_x (hm.trans r.symm))
    have zq := (split D.root_z).resolve_left (fun r=>D.h_ne_z (hm.trans r.symm))
    exact ⟨.centerLeftRight,x,xq,hm,rfl,comp xq zq D.x_ne_z⟩
  · rcases split D.root_x with xm|xq
    · have zq := (split D.root_z).resolve_left (fun r=>D.x_ne_z (xm.trans r.symm))
      exact ⟨.leftCenterRight,h,hq,rfl,xm,comp hq zq D.h_ne_z⟩
    · have xx := comp hq xq D.h_ne_x
      have zz := (split D.root_z).resolve_right (fun r=>D.x_ne_z (xx.trans (comp hq r D.h_ne_z).symm))
      exact ⟨.leftRightCenter,h,hq,rfl,xx,zz⟩

def chartScale (o : CleanOrientation) : K :=
  match o with
  | .leftCenterRight | .leftRightCenter => 28
  | .centerLeftRight => 308

def chartThetaNumer (o : CleanOrientation) (u : K) : K :=
  match o with
  | .leftCenterRight => 14-56*u
  | .leftRightCenter => 42-196*u
  | .centerLeftRight => 588-1568*u

def chartQuadratic (o : CleanOrientation) (u : K) : Quad K :=
  match o with
  | .leftCenterRight => ⟨3+21*u,-69-42*u,154-56*u⟩
  | .leftRightCenter => ⟨15-21*u,-147+168*u,182-196*u⟩
  | .centerLeftRight => ⟨84+84*u,-1050+336*u,2128-1568*u⟩

theorem chartScale_ne [EightUnits K] (p : (11:K)≠0) (o : CleanOrientation) :
    (chartScale (K:=K) o)≠0 := by
  have n28 : (28:K)≠0 := paidCastNe 28 (by decide)
  rcases o with _|_|_
  · exact n28
  · exact n28
  · change (308:K)≠0
    have eq : (308:K)=28*11 := by ring
    rw [eq]
    exact mul_ne_zero n28 p

theorem raw_has_shape_coefficients {P : K[X]} {h x z theta kap : K}
    (N : RawPaidShape P h x z theta kap) : HeadShapeCoeffs P h x z theta kap := by
  have clean : cleanPair x z=(X:K[X])^2-C (x+z)*X+C (x*z) := by
    simp only [cleanPair,map_add,map_mul]
    ring
  rw [N.identity,clean]
  have c1 (a : K) : (C a).coeff 1=0 := by simp
  have c2 (a : K) : (C a).coeff 2=0 := by simp
  constructor <;> simp only [shape,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_X,c1,c2,
    coeff_C_zero,show (0:ℕ)≠2 by decide,
    show (1:ℕ)≠2 by decide,show (1:ℕ)≠0 by decide,ite_true,ite_false,
    mul_zero,zero_mul,mul_one,one_mul,add_zero,zero_add,sub_zero,zero_sub] <;> ring

/-- A bounded-cast normalized head. It keeps the scale nonzero and
records coefficients, which is enough to handle both leading degrees. -/
structure ScaledPaidHead (P : K[X]) (o : CleanOrientation) (u kap : K) : Prop where
  scale_ne : chartScale (K:=K) o≠0
  kap_ne : kap≠0
  eq0 : chartScale o*P.coeff 0=kap*(chartQuadratic o u).p0
  eq1 : chartScale o*P.coeff 1=kap*(chartQuadratic o u).p1
  eq2 : chartScale o*P.coeff 2=kap*(chartQuadratic o u).p2

theorem ScaledPaidHead.eval {P : K[X]} {o : CleanOrientation} {u kap : K}
    (S : ScaledPaidHead P o u kap) (d : P.natDegree≤2) (t : K) :
    chartScale o*P.eval t=kap*(chartQuadratic o u).eval t := by
  conv_lhs => rw [LobattoEight.quadratic_coeff_expand P d]
  simp only [Quad.eval,eval_add,eval_monomial,pow_zero,pow_one,mul_one,one_mul,mul_add,
    ←mul_assoc,S.eq0,S.eq1,S.eq2]

theorem ScaledPaidHead.eval_zero_iff {P : K[X]} {o : CleanOrientation} {u kap : K}
    (S : ScaledPaidHead P o u kap) (d : P.natDegree≤2) (t : K) :
    P.eval t=0 ↔ (chartQuadratic o u).eval t=0 := by
  have e := S.eval d t
  constructor
  · intro z
    rw [z,mul_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_left S.kap_ne
  · intro z
    rw [z,mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left S.scale_ne

theorem ScaledPaidHead.degree_two {P : K[X]} {o : CleanOrientation} {u kap : K}
    (S : ScaledPaidHead P o u kap) (d : P.natDegree≤2)
    (p : (chartQuadratic o u).p2≠0) : P.natDegree=2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero d
  intro z
  exact mul_ne_zero S.kap_ne p (by simpa [z] using S.eq2.symm)

theorem ScaledPaidHead.degree_one {P : K[X]} {o : CleanOrientation} {u kap : K}
    (S : ScaledPaidHead P o u kap) (d : P.natDegree≤2)
    (z : (chartQuadratic o u).p2=0) (p : (chartQuadratic o u).p1≠0) :
    P.natDegree=1 := by
  have e := S.eq2
  rw [z,mul_zero] at e
  have v := (mul_eq_zero.mp e).resolve_left S.scale_ne
  have d1 := ERK8CharEleven.natDegree_le_of_last_coeff_zero (k:=1) d v
  apply natDegree_eq_of_le_of_coeff_ne_zero d1
  intro h
  exact mul_ne_zero S.kap_ne p (by simpa [h] using S.eq1.symm)

end RKResearch.Certified.Graded.FourOffNewton
