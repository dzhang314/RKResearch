module

public import RKCert.ReviewedNative.WeakFiveSoleOuterWords
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The unit root after the reverse inner mark is unique

Two left roots are paid by the first two moments. A third comes from
the true suffix. The remaining affine factor either has its root at or
below zero or contributes one more unit root below h. The seam where
the reflected profile vanishes exactly at zero is included. -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.FiniteRootSeparator RKCert.ReviewedNative.OrderedPolynomialSignStrips
open RKCert.ReviewedNative.RightPoleInterpolation
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem outer_integral_nonneg {P : K[X]} {l h : K} (lh : l < h) (dg : P.natDegree ≤ 19)
    (sign : ∀ x ∈ Set.Ioo l h, 0 ≤ P.eval x) : 0 ≤ integral l h P := by
  rw [interval_exact _ _ _ dg]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (intervalWeight_pos lh i).le
    (sign _ (intervalPoint_mem lh i))

theorem outer_integral_pos {P : K[X]} {l h : K} (lh : l < h) (dg : P.natDegree < 19)
    (pn : P ≠ 0) (sign : ∀ x ∈ Set.Ioo l h, 0 ≤ P.eval x) : 0 < integral l h P := by
  obtain ⟨i,hi⟩ := exists_nonzero_grid_sample lh pn dg
  exact integral_pos_of_grid_samples lh dg.le (fun j => sign _ (intervalPoint_mem lh j))
    ⟨i,lt_of_le_of_ne (sign _ (intervalPoint_mem lh i)) hi.symm⟩

theorem cut_list_nonzero (xs : List K) : cutProduct xs ≠ 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cutProduct_cons]
    exact mul_ne_zero (X_sub_C_ne_zero x) ih

theorem cut_list_pos_above (xs : List K) {x : K} (h : ∀ d ∈ xs, d < x) :
    0 < (cutProduct xs).eval x := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [cutProduct_cons,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos (sub_pos.mpr (h a (by simp))) (ih fun d hd => h d (List.mem_cons_of_mem _ hd))

theorem cut_list_has_root {xs : List K} {x : K} (h : x ∈ xs) :
    (cutProduct xs).IsRoot x := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    change (cutProduct (a::xs)).eval x = 0
    rcases List.mem_cons.mp h with eq | tail
    · subst a
      simp [cutProduct_cons]
    · rw [cutProduct_cons,eval_mul,show (cutProduct xs).eval x=0 from ih tail,mul_zero]

private theorem outer_three_roots {q : K[X]} {u a h z : K} (W : SoleOuterWords q u a h z)
    (G : GapComplete q) :
    ∃ l₁ l₂ r : K, 0 < l₁ ∧ l₁ < l₂ ∧ l₂ < u ∧ h < r ∧ r < 1 ∧
      q.IsRoot l₁ ∧ q.IsRoot l₂ ∧ q.IsRoot r := by
  obtain ⟨x,xo,xi,xs⟩ := finite_alternation_tuple (by decide) W.left_two
  obtain ⟨y,yo,yi,ys⟩ := finite_alternation_tuple (by decide) W.right_one
  have gx (i : Fin 2) := G (xo (Fin.castSucc_lt_succ (i:=i))) (mul_neg_iff.mp (xs i))
  obtain ⟨l₁,xlo,xhi,r₁⟩ := gx 0
  obtain ⟨l₂,ylo,yhi,r₂⟩ := gx 1
  obtain ⟨r,rlo,rhi,r₃⟩ := G (yo (by decide : (0:Fin 2)<1)) (mul_neg_iff.mp (ys 0))
  exact ⟨l₁,l₂,r,(xi 0).1.trans xlo,xhi.trans ylo,yhi.trans (xi 2).2,
    (yi 0).1.trans rlo,rhi.trans (yi 1).2,r₁,r₂,r₃⟩

private theorem fourth_root_shape {q : K[X]} {l₁ l₂ r : K} (m : q.Monic) (d : q.natDegree=4)
    (a : l₁<l₂) (b : l₂<r) (q₁ : q.IsRoot l₁) (q₂ : q.IsRoot l₂) (qr : q.IsRoot r) :
    ∃ e : K, q = ((X-C l₁)*(X-C l₂))*((X-C r)*(X-C e)) := by
  let t : Fin 3 → K := ![l₁,l₂,r]
  have sorted : StrictMono t := by
    intro i j ij
    fin_cases i <;> fin_cases j <;> norm_num at ij
    · exact a
    · exact a.trans b
    · exact b
  have roots (i : Fin 3) : q.IsRoot (t i) := by
    fin_cases i
    · exact q₁
    · exact q₂
    · exact qr
  obtain ⟨e, f⟩ := exists_indexed_linear_residual (t:=t) (S:=Finset.univ)
    (by simpa only [Finset.card_univ,Fintype.card_fin] using d) sorted.injective (fun i _ => roots i)
  refine ⟨e, ?_⟩
  calc
    q = C q.leadingCoeff*((X-C e)*indexedHull t Finset.univ) := f
    _ = _ := by
      simp only [m.leadingCoeff,map_one,one_mul,indexedHull,Fin.prod_univ_three]
      change (X-C e)*((X-C l₁)*(X-C l₂)*(X-C r))=_
      ring

/-- If the fourth root is on or to the right of h, the three truly
consecutive pieces of the reverse difference have one strictly positive sum. -/
private theorem fourth_root_cannot_lie_after_h {q : K[X]} {u a h z l₁ l₂ r e : K}
    (W : SoleOuterWords q u a h z) (l0 : 0<l₁) (ll : l₁<l₂) (lu : l₂<u)
    (rh : h<r) (he : h≤e)
    (fac : q=((X-C l₁)*(X-C l₂))*((X-C r)*(X-C e))) : False := by
  let P := (X-C l₁)*(X-C l₂)
  have pd : P.natDegree ≤ 2 := natDegree_mul_le_of_le (natDegree_X_sub_C _).le (natDegree_X_sub_C _).le
  have pn : P ≠ 0 := mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  have qv (x : K) : q.eval x = P.eval x*((x-r)*(x-e)) := by
    simpa only [P,eval_mul,eval_sub,eval_X,eval_C] using congrArg (Polynomial.eval x) fac
  have ppos (x : K) (h₁ : l₁<x) (h₂ : l₂<x) : 0<P.eval x := by
    simp only [P,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂)
  have pbefore (x : K) (h₁ : x<l₁) (h₂ : x<l₂) : 0<P.eval x := by
    simp only [P,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr h₁) (sub_neg.mpr h₂)
  have leftPositive : 0 < integral 0 u (q*P) := by
    apply outer_integral_pos W.uUnit.1 ((natDegree_mul_le_of_le W.degree.le pd).trans_lt (by decide : 6<19))
      (mul_ne_zero W.monic.ne_zero pn)
    intro x hx
    rw [eval_mul,qv,show P.eval x*((x-r)*(x-e))*P.eval x=(P.eval x)^2*((x-r)*(x-e)) by ring]
    exact mul_nonneg (sq_nonneg _) (mul_pos_of_neg_of_neg
      (sub_neg.mpr (hx.2.trans (W.uh.trans rh))) (sub_neg.mpr (hx.2.trans (W.uh.trans_le he)))).le
  have lhs : q*P=X^2*q-C (l₁+l₂)*(X*q)+C (l₁*l₂)*q := by
    simp only [P,map_add,map_mul]
    ring
  rw [lhs,map_add,map_sub,integral_C_mul,integral_C_mul,W.leftFirst,W.leftSecond,
    mul_zero,sub_zero,zero_add] at leftPositive
  have mean : 0 < integral 0 u q :=
    pos_of_mul_pos_right leftPositive (mul_pos l0 (l0.trans ll)).le
  let V := (1-X)*(X-C z)*q
  have vd : V.natDegree ≤ 6 := natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (unit_right_weight_degree (K:=K)).le (natDegree_X_sub_C _).le) W.degree.le
  have v19 : V.natDegree ≤ 19 := vd.trans (by decide)
  have dv (x : K) : V.eval x=(1-x)*(x-z)*q.eval x := by
    simp only [V,eval_mul,eval_sub,eval_one,eval_X,eval_C]
  have start : 0 ≤ integral z 0 V := by
    apply outer_integral_nonneg W.zNeg v19
    intro x hx
    rw [dv,qv]
    have xh : x<h := hx.2.trans W.hUnit.1
    exact mul_nonneg (mul_pos (sub_pos.mpr (hx.2.trans zero_lt_one)) (sub_pos.mpr hx.1)).le
      (mul_pos (pbefore x (hx.2.trans l0) (hx.2.trans (l0.trans ll)))
        (mul_pos_of_neg_of_neg (sub_neg.mpr (xh.trans rh)) (sub_neg.mpr (xh.trans_le he)))).le
  have ending : 0 ≤ integral u h V := by
    apply outer_integral_nonneg W.uh v19
    intro x hx
    rw [dv,qv]
    exact mul_nonneg (mul_pos (sub_pos.mpr (hx.2.trans W.hUnit.2))
      (sub_pos.mpr (W.zNeg.trans (W.uUnit.1.trans hx.1)))).le
      (mul_pos (ppos x (ll.trans (lu.trans hx.1)) (lu.trans hx.1))
        (mul_pos_of_neg_of_neg (sub_neg.mpr (hx.2.trans rh)) (sub_neg.mpr (hx.2.trans_le he)))).le
  have core : 0 < integral 0 u V := by
    have ev : V = C (1+z)*(X*q)-X^2*q+C (-z)*q := by
      simp only [V,map_add,map_one,map_neg]
      ring
    rw [ev,map_add,map_sub,integral_C_mul,integral_C_mul,W.leftFirst,W.leftSecond,
      mul_zero,sub_zero,zero_add]
    exact mul_pos (neg_pos.mpr W.zNeg) mean
  have h₁ := exact_integral_join V z 0 u
  have h₂ := exact_integral_join V z u h
  have hz : integral z h V=0 := W.right_difference
  have positive₁ : 0 < integral z u V :=
    h₁ ▸ add_pos_of_nonneg_of_pos start core
  have positive₂ : 0 < integral z h V :=
    h₂ ▸ add_pos_of_pos_of_nonneg positive₁ ending
  exact (ne_of_gt positive₂) hz

structure OuterUnitSplit (q B : K[X]) (xs : List K) (r u h : K) : Prop where
  late : r ∈ Set.Ioo h 1
  early : ∀ x ∈ xs, x ∈ Set.Ioo 0 h
  leftLive : ∃ x ∈ xs, x<u
  lower : 2 ≤ xs.length
  upper : xs.length+ B.natDegree ≤ 3
  positive : ∀ x ∈ Set.Ioo 0 1, 0 < B.eval x
  factor : q = B*cutProduct xs*(X-C r)

theorem sole_outer_unit_split {q : K[X]} {u a h z : K} (W : SoleOuterWords q u a h z)
    (G : GapComplete q) : ∃ (B : K[X]) (xs : List K) (r : K), OuterUnitSplit q B xs r u h := by
  obtain ⟨l₁,l₂,r,l0,ll,lu,hl,r1,q₁,q₂,qr⟩ := outer_three_roots W G
  have lh : l₁ < h := ll.trans (lu.trans W.uh)
  have l₂h : l₂ < h := lu.trans W.uh
  obtain ⟨e,hf⟩ := fourth_root_shape W.monic W.degree ll (l₂h.trans hl) q₁ q₂ qr
  by_cases e0 : e ≤ 0
  · refine ⟨X-C e,[l₁,l₂],r,⟨⟨hl,r1⟩,?_,⟨l₁,by simp,ll.trans lu⟩,by change 2 ≤ 2; decide,?_,?_,?_⟩⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨l0,lh⟩
      · exact ⟨l0.trans ll,l₂h⟩
    · simp [natDegree_X_sub_C]
    · intro x hx
      simpa only [eval_X,eval_sub,eval_C] using sub_pos.mpr (e0.trans_lt hx.1)
    · rw [hf]
      simp only [cutProduct_cons,cutProduct_nil,mul_one]
      ring
  · have eh : e < h := lt_of_not_ge (fun bad =>
      fourth_root_cannot_lie_after_h W l0 ll lu hl bad hf)
    refine ⟨1,[l₁,l₂,e],r,⟨⟨hl,r1⟩,?_,⟨l₁,by simp,ll.trans lu⟩,by change 2 ≤ 3; decide,by simp,by simp,?_⟩⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨l0,lh⟩
      · exact ⟨l0.trans ll,l₂h⟩
      · exact ⟨lt_of_not_ge e0,eh⟩
    · rw [hf]
      simp only [cutProduct_cons,cutProduct_nil,mul_one,one_mul]
      ring

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
