module

public import RKCert.ReviewedNative.WeakFiveSoleOuterRootLayout

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The forward inner mark is strictly to the right of h

The comparison spends one proved global test and the true reverse inner
zero. It does not rely on a synthetic choice of a window after h. -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.RightPoleInterpolation
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem cut_list_append (xs ys : List K) :
    cutProduct (xs++ys) = cutProduct xs*cutProduct ys := by
  simp only [cutProduct,List.map_append,List.prod_append]

theorem cut_list_monotone_above (xs : List K) {x y : K} (xy : x≤y)
    (loc : ∀ v∈xs, v<x) : (cutProduct xs).eval x ≤ (cutProduct xs).eval y := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have below : ∀ d∈xs,d<x := fun d hd => loc d (List.mem_cons_of_mem _ hd)
    simp only [cutProduct_cons,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_le_mul (sub_le_sub_right xy a) (ih below) (cut_list_pos_above xs below).le
      (sub_nonneg.mpr ((loc a (by simp)).le.trans xy))

theorem raw_four_hull_degree (u a h z : K) : (rawFourHull u a h z).natDegree ≤ 4 := by
  unfold rawFourHull
  exact natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (natDegree_X_sub_C u).le (natDegree_X_sub_C z).le)
    (natDegree_mul_le_of_le (natDegree_X_sub_C a).le (natDegree_X_sub_C h).le)

theorem raw_four_hull_ne_zero (u a h z : K) : rawFourHull u a h z ≠ 0 := by
  unfold rawFourHull
  exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
    (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))

theorem outer_unit_bubble_degree : (X*(1-X) : K[X]).natDegree ≤ 2 :=
  natDegree_mul_le_of_le natDegree_X.le (unit_right_weight_degree (K:=K)).le

theorem outer_unit_bubble_ne_zero : (X*(1-X) : K[X]) ≠ 0 := by
  apply mul_ne_zero X_ne_zero
  intro eq
  have h := unit_right_weight_degree (K:=K)
  rw [eq,natDegree_zero] at h
  exact Nat.zero_ne_one h

theorem sole_outer_forward_inner_after_h {q B : K[X]} {xs : List K} {u a h z r : K}
    (W : SoleOuterWords q u a h z) (L : OuterUnitSplit q B xs r u h) : h<a := by
  by_contra! ah
  have ah' : a<h := lt_of_le_of_ne ah W.aNeH
  have cnt := L.upper
  let P := cutProduct xs
  let fit := P*(X-C u)*(X-C a)
  let T := (X*(1-X))*(q*rawFourHull u a h z)*fit
  have pd : P.natDegree≤3 := (cutProduct_degree xs).trans (by omega)
  have fd : fit.natDegree≤5 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le pd (natDegree_X_sub_C _).le) (natDegree_X_sub_C _).le
  have td : T.natDegree≤15 := natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (outer_unit_bubble_degree (K:=K))
      (natDegree_mul_le_of_le W.degree.le (raw_four_hull_degree u a h z))) fd
  have Tn : T≠0 := mul_ne_zero
    (mul_ne_zero (outer_unit_bubble_ne_zero (K:=K)) (mul_ne_zero W.monic.ne_zero (raw_four_hull_ne_zero u a h z)))
    (mul_ne_zero (mul_ne_zero (cut_list_nonzero xs) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _))
  have paid : integral 0 1 T=0 := W.global fit fd
  have qp (x : K) : q.eval x=B.eval x*P.eval x*(x-r) := by
    simpa only [P,eval_mul,eval_sub,eval_C,eval_X] using congrArg (Polynomial.eval x) L.factor
  have lp : 0 < integral 0 h T := by
    apply outer_integral_pos W.hUnit.1 (td.trans_lt (by decide)) Tn
    intro x hx
    have ex : T.eval x =
        ((x*(1-x)*(x-z))*B.eval x)*((P.eval x)^2*(x-u)^2*(x-a)^2)*((x-h)*(x-r)) := by
      simp only [T,fit,rawFourHull,eval_mul,eval_sub,eval_one,eval_X,eval_C,qp]
      ring
    rw [ex]
    have x1 : x<1 := hx.2.trans W.hUnit.2
    exact mul_nonneg
      (mul_nonneg (mul_pos (mul_pos (mul_pos hx.1 (sub_pos.mpr x1))
        (sub_pos.mpr (W.zNeg.trans hx.1))) (L.positive x ⟨hx.1,x1⟩)).le
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)))
      (mul_pos_of_neg_of_neg (sub_neg.mpr hx.2) (sub_neg.mpr (hx.2.trans L.late.1))).le
  let V := (1-X)*(X-C z)*q
  let cuts := [0,h,u,u,a,a]++xs
  let D := cutProduct cuts
  have Dexp : D=X*(X-C h)*(X-C u)^2*(X-C a)^2*P := by
    simp only [D,cuts,cut_list_append,cutProduct_cons,cutProduct_nil,map_zero,sub_zero,mul_one,P]
    ring
  have applyD : T=V*D := by
    simp only [T,V,fit,rawFourHull,Dexp]
    ring
  have subtract : integral h 1 (V*(D-C (D.eval r)))=integral h 1 T := by
    rw [applyD,mul_sub,map_sub,show V*C (D.eval r)=C (D.eval r)*V by ring,
      integral_C_mul,show integral h 1 V=0 from W.rightInner,mul_zero,sub_zero]
  have vd : V.natDegree≤6 := natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (unit_right_weight_degree (K:=K)).le (natDegree_X_sub_C _).le) W.degree.le
  have dd : D.natDegree≤9 := (cutProduct_degree cuts).trans (by
    change ([0,h,u,u,a,a]++xs).length≤9
    simp only [List.length_append,List.length_cons,List.length_nil]
    have := L.upper
    omega)
  have top : (V*(D-C (D.eval r))).natDegree≤15 := natDegree_mul_le_of_le vd
    (natDegree_sub_le_of_le dd ((natDegree_C (D.eval r)).trans_le (Nat.zero_le 9)))
  have rightPos : 0 ≤ integral h 1 T := by
    rw [← subtract]
    apply outer_integral_nonneg W.hUnit.2 (top.trans (by decide))
    intro x hx
    have xb : ∀ v∈cuts,v<x := by
      intro v hv
      rcases List.mem_append.mp hv with l | e
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at l
        rcases l with rfl | rfl | rfl | rfl | rfl | rfl
        · exact W.hUnit.1.trans hx.1
        · exact hx.1
        · exact W.uh.trans hx.1
        · exact W.uh.trans hx.1
        · exact ah'.trans hx.1
        · exact ah'.trans hx.1
      · exact (L.early v e).2.trans hx.1
    have rb : ∀ v∈cuts,v<r := by
      intro v hv
      rcases List.mem_append.mp hv with l | e
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at l
        rcases l with rfl | rfl | rfl | rfl | rfl | rfl
        · exact W.hUnit.1.trans L.late.1
        · exact L.late.1
        · exact W.uh.trans L.late.1
        · exact W.uh.trans L.late.1
        · exact ah'.trans L.late.1
        · exact ah'.trans L.late.1
      · exact (L.early v e).2.trans L.late.1
    have x0 : 0<x := W.hUnit.1.trans hx.1
    have k : 0≤(1-x)*(x-z)*B.eval x*P.eval x := by
      exact (mul_pos (mul_pos (mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr (W.zNeg.trans x0)))
        (L.positive x ⟨x0,hx.2⟩)) (cut_list_pos_above xs (fun v hv => (L.early v hv).2.trans hx.1))).le
    have agree : 0≤(x-r)*(D.eval x-D.eval r) := by
      rcases le_total x r with le | le
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr le)
          (sub_nonpos.mpr (cut_list_monotone_above cuts le xb))
      · exact mul_nonneg (sub_nonneg.mpr le)
          (sub_nonneg.mpr (cut_list_monotone_above cuts le rb))
    have ex : (V*(D-C (D.eval r))).eval x =
        ((1-x)*(x-z)*B.eval x*P.eval x)*((x-r)*(D.eval x-D.eval r)) := by
      simp only [V,eval_mul,eval_sub,eval_one,eval_C,eval_X,qp]
      ring
    rw [ex]
    exact mul_nonneg k agree
  have sum := exact_integral_join T 0 h 1
  linarith only [sum,paid,lp,rightPos]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
