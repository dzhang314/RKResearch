module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveRemainingScalarCases
public import RKCert.ReviewedNative.OrderedRightPoleInterpolation
public import RKCert.ReviewedNative.FiniteStoppedBracket

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Seam-safe physical windows for the sole outer exterior clock -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.FiniteRootSeparator
open scoped Polynomial

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Left-exterior orientation. Only the off-stop conditions actually used
are kept. In particular q(0) and q(1) are allowed to be zero. -/
structure SoleOuterWords (q : K[X]) (u a h z : K) : Prop where
  monic : q.Monic
  degree : q.natDegree = 4
  uUnit : u ∈ Set.Ioo 0 1
  aUnit : a ∈ Set.Ioo 0 1
  hUnit : h ∈ Set.Ioo 0 1
  zNeg : z < 0
  uh : u < h
  aNeH : a ≠ h
  uActive : q.eval u ≠ 0
  hActive : q.eval h ≠ 0
  leftFirst : integral 0 u (X*q) = 0
  leftSecond : integral 0 u (X^2*q) = 0
  rightFirst : integral z 1 ((1-X)*q) = 0
  rightSecond : integral z 1 ((1-X)^2*q) = 0
  rightInner : integral h 1 ((1-X)*(X-C z)*q) = 0
  global : PaidSix q u a h z

theorem exterior_left_words {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (monic : q.Monic)
    (z : c 4 < 0) (u : MarkInterior c 1) (a : MarkInterior c 2) (h : MarkInterior c 3)
    (order : c 1 < c 3) :
    SoleOuterWords q (c 1) (c 2) (c 3) (c 4) := by
  refine ⟨monic,M.natDegree_eq_four_of_full_packet,u,a,h,z,order,
    fun e => (by decide : (2 : Fin 5) ≠ 3) (M.clockSimple e), (M.active 1).2,(M.active 3).2,
    M.forwardFirst,M.forwardSecond,M.reverseFirst,M.reverseSecond,?_,paidSix_of_actual_moments M⟩
  rw [show (1-X)*(X-C (c 4))*q= -((1-X)*(C (c 4)-X)*q) by ring,
    map_neg,M.reverseInner,neg_zero]

private theorem flip_twice (P : K[X]) : (P.comp (1-X)).comp (1-X)=P := by
  rw [comp_assoc,show (1-X : K[X]).comp (1-X)=X by
    simp only [sub_comp,one_comp,X_comp,sub_sub_cancel],comp_X]

private theorem flip_suffix (P : K[X]) (x : K) :
    integral (1-x) 1 (P.comp (1-X)) = integral 0 x P := by
  calc
    _ = integral 0 x ((P.comp (1-X)).comp (1-X)) := by
      simpa only [sub_sub_cancel] using (integral_reflect (P.comp (1-X)) (1-x)).symm
    _ = integral 0 x P := congrArg (fun Q : K[X] => integral 0 x Q) (flip_twice P)

/-- Mirror the genuine right-exterior source without repackaging it as
`Moments` at a potentially vanishing reflected origin. -/
theorem exterior_right_words {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (mono : q.Monic)
    (u : 1 < c 1) (a : MarkInterior c 2) (h : MarkInterior c 3) (z : MarkInterior c 4)
    (order : c 2 < c 4) :
    SoleOuterWords (q.comp (1-X)) (1-c 4) (1-c 3) (1-c 2) (1-c 1) := by
  have nz : (1-X : K[X]).natDegree ≠ 0 := by rw [unit_right_weight_degree]; decide
  have lc : (1-X : K[X]).leadingCoeff = -1 := by
    rw [show (1-X : K[X]) = -(X-C (1:K)) by simp [neg_sub], leadingCoeff_neg,leadingCoeff_X_sub_C]
  have even := M.natDegree_eq_four_of_full_packet
  have qMono : (q.comp (1-X)).Monic := by
    change (q.comp (1-X)).leadingCoeff=1
    rw [leadingCoeff_comp nz,mono.leadingCoeff,lc,even]
    norm_num
  have deg : (q.comp (1-X)).natDegree=4 := by rw [natDegree_comp,unit_right_weight_degree,mul_one,even]
  have uI {t : K} (hi : t ∈ Set.Ioo 0 1) : 1-t ∈ Set.Ioo 0 1 :=
    ⟨sub_pos.mpr hi.2,by linarith only [hi.1]⟩
  have hNe : (1-c 3) ≠ (1-c 2) := fun e =>
    (by decide : (3 : Fin 5) ≠ 2) (M.clockSimple (by linarith only [e]))
  have active (i : Fin 5) : (q.comp (1-X)).eval (1-c i) ≠ 0 := by
    simpa only [eval_comp,eval_sub,eval_one,eval_X,sub_sub_cancel] using (M.active i).2
  refine ⟨qMono,deg,uI z,uI h,uI a,sub_neg.mpr u,sub_lt_sub_left order 1,hNe,active 4,active 2,
    ?_,?_,?_,?_,?_,reflected_paidSix M⟩
  · simpa only [mul_comp,sub_comp,one_comp,X_comp,sub_sub_cancel] using
      (integral_reflect ((1-X)*q) (c 4)).trans M.reverseFirst
  · simpa only [mul_comp,pow_comp,sub_comp,one_comp,X_comp,sub_sub_cancel] using
      (integral_reflect ((1-X)^2*q) (c 4)).trans M.reverseSecond
  · simpa only [mul_comp,X_comp] using (flip_suffix (X*q) (c 1)).trans M.forwardFirst
  · simpa only [mul_comp,pow_comp,X_comp] using (flip_suffix (X^2*q) (c 1)).trans M.forwardSecond
  · have shape : (X*(X-C (c 1))*q).comp (1-X) =
        (1-X)*(X-C (1-c 1))*q.comp (1-X)*(-1) := by
      simp only [mul_comp,sub_comp,X_comp,C_comp,map_sub,map_one]
      ring
    have H := (flip_suffix (X*(X-C (c 1))*q) (c 2)).trans M.forwardInner
    have alt : (X*(X-C (c 1))*q).comp (1-X) =
        -((1-X)*(X-C (1-c 1))*q.comp (1-X)) := by rw [shape,mul_neg,mul_one]
    rw [alt,map_neg,neg_eq_zero] at H
    exact H

theorem gap_complete_flip {p : K[X]} (G : GapComplete p) : GapComplete (p.comp (1-X)) := by
  intro a b ab op
  have eq (x : K) : (p.comp (1-X)).eval x = p.eval (1-x) := by simp [eval_comp]
  rw [eq a,eq b] at op
  have rot : Opposite (p.eval (1-b)) (p.eval (1-a)) := by
    rcases op with h | h
    · exact Or.inr ⟨h.2,h.1⟩
    · exact Or.inl ⟨h.2,h.1⟩
  obtain ⟨r,lo,hi,rt⟩ := G (sub_lt_sub_left ab 1) rot
  refine ⟨1-r,by linarith only [hi],by linarith only [lo],?_⟩
  change (p.comp (1-X)).eval (1-r)=0
  rw [eq,sub_sub_cancel]
  exact rt

theorem SoleOuterWords.left_two {q : K[X]} {u a h z : K} (W : SoleOuterWords q u a h z) :
    HasAlternationsOn q (Set.Ioo 0 u) 2 := by
  refine variation_of_affine_tests W.uUnit.1 W.monic.ne_zero W.degree.le natDegree_X.le ?_ W.leftFirst ?_
  · intro x hx
    simpa only [eval_X] using hx.1
  · rw [show X*q*X=X^2*q by ring]
    exact W.leftSecond

theorem SoleOuterWords.right_one {q : K[X]} {u a h z : K} (W : SoleOuterWords q u a h z) :
    HasAlternationsOn q (Set.Ioo h 1) 1 := by
  refine variation_of_one_test W.hUnit.2 W.monic.ne_zero W.degree.le
    (natDegree_mul_le_of_le (unit_right_weight_degree (K:=K)).le (natDegree_X_sub_C _).le)
    ?_ W.rightInner
  intro x hx
  simp only [eval_mul,eval_sub,eval_one,eval_X,eval_C]
  exact mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr (W.zNeg.trans (W.hUnit.1.trans hx.1)))

theorem SoleOuterWords.right_difference {q : K[X]} {u a h z : K} (W : SoleOuterWords q u a h z) :
    integral z h ((1-X)*(X-C z)*q) = 0 := by
  let V := (1-X)*(X-C z)*q
  have large : integral z 1 V=0 := by
    rw [show V = C (1-z)*((1-X)*q)-(1-X)^2*q by simp only [V,map_sub,map_one]; ring,
      map_sub,integral_C_mul,W.rightFirst,W.rightSecond,mul_zero,sub_zero]
  have join := exact_integral_join V z h 1
  rw [show integral h 1 V=0 from W.rightInner,large,add_zero] at join
  exact join

theorem SoleOuterWords.left_tilt_zero {q : K[X]} {u a h z : K}
    (W : SoleOuterWords q u a h z) (v : K) : integral 0 u (X*(X-C v)*q)=0 := by
  rw [show X*(X-C v)*q=X^2*q-C v*(X*q) by ring,map_sub,integral_C_mul,
    W.leftFirst,W.leftSecond,mul_zero,sub_zero]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
