module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorWindows
public import RKCert.ReviewedNative.FiniteStoppedBracket

import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Degree-paid stopped brackets after one actual erasure

A genuine four-cut fitting polynomial supplies the separator. The exact law
on the three retained atoms has eight paid degrees and produces an opposite
mass on the open stopped side. Suffixes use only an exact reflection, not a
fictional active origin.
-/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.RightPoleInterpolation
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open RKCert.ReviewedNative.FiniteStoppedBracket RKCert.ReviewedNative.FiniteGaussianNodalLift
open scoped Polynomial BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem cut_above_pos (L : List K) (x : K) (above : ∀ y ∈ L, y < x) :
    0 < (cutProduct L).eval x := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [cutProduct_cons,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos (sub_pos.mpr (above a (by simp)))
      (ih (fun y hy => above y (List.mem_cons_of_mem a hy)))

private theorem separator_from_unit_factor {P S : K[X]} {t : K} {L R : List K}
    (t0 : 0 < t) (t1 : t < 1) (sh : P = S*cutProduct L*cutProduct R)
    (pos : ∀ x ∈ Set.Ioo (0:K) 1, 0 < S.eval x)
    (below : ∀ x ∈ L, x < t) (above : ∀ x ∈ R, t < x) :
    StopSeparator P 0 t 1 ((-1:K)^R.length) L R := by
  let τ : K := (-1)^R.length
  have τsq : τ*τ = 1 := by
    dsimp only [τ]
    rw [← mul_pow]
    norm_num
  refine ⟨below,above,?_,?_⟩
  · intro j live
    let x := intervalPoint 0 t j
    have xh : x ∈ Set.Ioo (0:K) t := intervalPoint_mem t0 j
    have ln : (cutProduct L).eval x ≠ 0 := by
      intro z
      apply live
      change P.eval x = 0
      rw [sh,eval_mul,eval_mul,z,mul_zero,zero_mul]
    have eq : τ*P.eval x*(cutProduct L).eval x =
        S.eval x*((cutProduct L).eval x)^2*(poleProduct R).eval x := by
      rw [sh,eval_mul,eval_mul,poleProduct_orientation]
      dsimp only [τ]
      ring
    change 0 < τ*P.eval x*(cutProduct L).eval x
    rw [eq]
    exact mul_pos (mul_pos (pos x ⟨xh.1,xh.2.trans t1⟩) (sq_pos_of_ne_zero ln))
      (poleProduct_pos R x (fun y hy => xh.2.trans (above y hy)))
  · intro j live
    let x := intervalPoint t 1 j
    have xh : x ∈ Set.Ioo t (1:K) := intervalPoint_mem t1 j
    have rn : (cutProduct R).eval x ≠ 0 := by
      intro z
      apply live
      change P.eval x = 0
      rw [sh,eval_mul,z,mul_zero]
    change 0 < (τ*τ)*P.eval x*(cutProduct R).eval x
    rw [τsq,one_mul,sh,eval_mul,eval_mul,mul_assoc,← pow_two]
    exact mul_pos
      (mul_pos (pos x ⟨t0.trans xh.1,xh.2⟩)
        (cut_above_pos L x (fun y hy => (below y hy).trans xh.1)))
      (sq_pos_of_ne_zero rn)

/-- Four actual cuts, strictly separated by a live stop, provide the
whole finite separator with the exact count four. -/
private theorem actual_four_cut_separator {P S : K[X]} {t : K} (c : Fin 4 → K)
    (t0 : 0 < t) (t1 : t < 1) (fact : P = S*indexedHull c Finset.univ)
    (pos : ∀ x ∈ Set.Ioo (0:K) 1, 0 < S.eval x) (off : ∀ j, c j ≠ t) :
    ∃ L R : List K, L.length+R.length = 4 ∧
      StopSeparator P 0 t 1 ((-1:K)^R.length) L R := by
  let A : List K := (Finset.univ : Finset (Fin 4)).toList.map c
  let f (x : K) : Bool := decide (x < t)
  let L := A.filter f
  let R := A.filter (fun x => !f x)
  have perm : (L++R).Perm A := List.filter_append_perm f A
  have aLen : A.length = 4 := by simp [A]
  have cutLen : L.length+R.length = 4 := by
    simpa only [List.length_append,aLen] using perm.length_eq
  have lower (x : K) (hx : x ∈ L) : x < t :=
    of_decide_eq_true (List.mem_filter.mp hx).2
  have upper (x : K) (hx : x ∈ R) : t < x := by
    have no : ¬ x < t := by
      intro lt
      have b := (List.mem_filter.mp hx).2
      simp only [f,decide_eq_true lt,Bool.not_true,Bool.false_eq_true] at b
    obtain ⟨j, _, e⟩ := List.mem_map.mp (List.mem_filter.mp hx).1
    exact lt_of_le_of_ne (le_of_not_gt no) (fun z => off j (e.trans z.symm))
  have eq : cutProduct L*cutProduct R = indexedHull c Finset.univ := by
    have h := (perm.map (fun x : K => (X:K[X])-C x)).prod_eq
    simpa only [List.map_append,List.prod_append,A,cutProduct,List.map_map,
      Finset.prod_map_toList,Function.comp_apply,indexedHull] using h
  have sh : P = S*cutProduct L*cutProduct R := by rw [mul_assoc,eq]; exact fact
  exact ⟨L,R,cutLen,separator_from_unit_factor t0 t1 sh pos lower upper⟩

/-- The exact erased law produces a strictly opposite remaining atom
on the open prefix. The degree charges in the generic bracket are 8
(global test), at most 15 (positive grid), and at most 7 (nonzero survival). -/
theorem threeInterior_prefix_opposite_of_erasure {v ω : Fin 4 → K} {e t : Fin 4}
    (he : t ≠ e) (in_unit : ∀ i, v i ∈ Set.Ioo 0 1) (inj : Function.Injective v)
    {P S : K[X]} (cuts : Fin 4 → K) (off : ∀ i, cuts i ≠ v t)
    (fact : P = S*indexedHull cuts Finset.univ)
    (pos : ∀ x ∈ Set.Ioo (0:K) 1, 0 < S.eval x) (pd : P.natDegree ≤ 5)
    (law : ExactRule (weighted (integral 0 1) (X*(1-X)*P))
      (Finset.univ.erase e) v ω 8)
    (paid : integral 0 (v t) (X*P) = 0) :
    ∃ i : Fin 4, i ≠ t ∧ i ≠ e ∧ v i < v t ∧ ω i*ω t < 0 := by
  classical
  have t0 := (in_unit t).1
  have t1 := (in_unit t).2
  obtain ⟨L,R,cutLen,sep⟩ := actual_four_cut_separator cuts t0 t1 fact pos off
  let σ : K := (-1)^R.length
  let Z : Finset (Fin 4) := Finset.univ.erase e
  let T : Finset (Fin 4) := Z.erase t
  have htZ : t ∈ Z := Finset.mem_erase.mpr ⟨he,Finset.mem_univ _⟩
  let f (i : Fin 4) : Bool := decide (v i < v t)
  let leftI := T.toList.filter f
  let rightI := T.toList.filter (fun i => !f i)
  let left := leftI.map v
  let right := rightI.map v
  let μ (x : K) : K := ω (Function.invFun v x)
  have atom (i : Fin 4) : μ (v i) = ω i := by
    simp only [μ,Function.leftInverse_invFun inj i]
  have ihave (i : Fin 4) (hi : i ∈ T.toList) : i ≠ t ∧ i ≠ e := by
    have hit : i ∈ Z.erase t := Finset.mem_toList.mp hi
    obtain ⟨it,iZ⟩ := Finset.mem_erase.mp hit
    have raw : i ∈ Finset.univ.erase e := iZ
    exact ⟨it,(Finset.mem_erase.mp raw).1⟩
  have atomsLeft (x : K) (hx : x ∈ left) : x < v t := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  have atomsRight (x : K) (hx : x ∈ right) : v t < x := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have h := List.mem_filter.mp hi
    have no : ¬ v i < v t := by
      intro lt
      have b := h.2
      simp only [f,decide_eq_true lt,Bool.not_true,Bool.false_eq_true] at b
    refine lt_of_le_of_ne (le_of_not_gt no) (fun eq => ?_)
    exact (ihave i h.1).1 (inj eq.symm)
  have card2 : T.card = 2 := by
    change (Z.erase t).card = 2
    rw [Finset.card_erase_of_mem htZ]
    change ((Finset.univ : Finset (Fin 4)).erase e).card - 1 = 2
    rw [Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ, Fintype.card_fin]
  have partition : (leftI++rightI).Perm T.toList := List.filter_append_perm f _
  have partLengths : left.length+right.length = 2 := by
    simpa only [left,right,List.length_map,List.length_append,Finset.length_toList,card2]
      using partition.length_eq
  have ppos : S ≠ 0 := by
    intro z
    have h := pos (v t) (in_unit t)
    rw [z,eval_zero] at h
    exact (lt_irrefl (0:K)) h
  have pn : P ≠ 0 := by rw [fact]; exact mul_ne_zero ppos (indexedHull_monic cuts Finset.univ).ne_zero
  have poles : poleProduct ([1] : List K) = (1-X : K[X]) := by simp [poleProduct]
  have degPole : (poleProduct ([1] : List K)).natDegree = 1 := by
    rw [poles]
    exact unit_right_weight_degree (K := K)
  have atomList (I : List (Fin 4)) (w : K → K) :
      atomSum (I.map v) μ w = (I.map (fun i => ω i*w (v i))).sum := by
    unfold atomSum
    rw [List.map_map]
    apply congrArg List.sum
    apply congrArg (fun a : Fin 4 → K => I.map a)
    funext i
    simp only [Function.comp_apply,atom]
  have glob (B : K[X]) (bd : B.natDegree ≤ 8) :
      integral 0 1 (X*poleProduct [1]*P*B) =
        atomSum left μ B.eval + μ (v t)*B.eval (v t) + atomSum right μ B.eval := by
    have h := law B bd
    change integral 0 1 (X*(1-X)*P*B) = _ at h
    let test (i : Fin 4) := ω i*B.eval (v i)
    have split := ((partition.map test).sum_eq)
    simp only [List.map_append,List.sum_append,Finset.sum_map_toList] at split
    calc
      integral 0 1 (X*poleProduct [1]*P*B) = ∑ i ∈ Z, test i := by rw [poles]; exact h
      _ = (∑ i ∈ T, test i)+test t := (Finset.sum_erase_add _ _ htZ).symm
      _ = atomSum left μ B.eval + μ (v t)*B.eval (v t) + atomSum right μ B.eval := by
        dsimp only [left, right]
        rw [atomList, atomList, atom, ← split]
        dsimp only [test]
        ring
  have survive : P.natDegree+left.length < 19 := by omega
  have localDegree : ((X:K[X])*P).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le natDegree_X.le pd).trans (by decide)
  have charge : bracketDegree L R left right ≤ 8 := by
    unfold bracketDegree
    omega
  have grid : (X:K[X]).natDegree+(poleProduct ([1]:List K)).natDegree+P.natDegree+
      bracketDegree L R left right ≤ 19 := by
    rw [natDegree_X,degPole]
    omega
  have signed := strict_bracket_of_pole_grid (A := (X : K[X])) (b := 8) t0 t1 [1] L R left right
    (by simp) (by simp) sep atomsLeft atomsRight
    (fun i => by rw [eval_X]; exact (intervalPoint_mem t0 i).1)
    (fun i => by rw [eval_X]; exact (t0.trans (intervalPoint_mem t1 i).1).le)
    pn survive localDegree charge grid glob paid
  let h (x : K) := ((poleProduct ([1] : List K)).eval x)⁻¹
  have hp (i : Fin 4) : 0 < h (v i) :=
    inv_pos.mpr (poleProduct_pos [1] _ (fun y hy => by
      obtain rfl : y = (1:K) := by simpa using hy
      exact (in_unit i).2))
  have sneg : σ*atomSum left μ h < 0 := signed.1
  have spos : 0 < σ*(atomSum left μ h+μ (v t)*h (v t)) := signed.2
  have mark_t : 0 < σ*ω t := by
    have ps : 0 < σ*(μ (v t)*h (v t)) := by rw [mul_add] at spos; linarith only [sneg,spos]
    rw [← mul_assoc,atom] at ps
    exact (mul_pos_iff_of_pos_right (hp t)).mp ps
  have sublive : ∃ i ∈ leftI, σ*ω i < 0 := by
    by_contra! none
    have sum_nonneg (I : List (Fin 4)) (hI : ∀ j ∈ I, 0 ≤ σ*ω j) :
        0 ≤ σ*atomSum (I.map v) μ h := by
      induction I with
      | nil => simp [atomSum]
      | cons i I ih =>
        have hn := ih (fun j hj => hI j (List.mem_cons_of_mem _ hj))
        rw [List.map_cons,show atomSum (v i :: I.map v) μ h =
          μ (v i)*h (v i)+atomSum (I.map v) μ h from rfl,mul_add,← mul_assoc,atom]
        exact add_nonneg (mul_nonneg (hI i (by simp)) (hp i).le) hn
    exact (not_lt_of_ge (sum_nonneg leftI none)) sneg
  obtain ⟨i,hi,neg⟩ := sublive
  have ne := ihave i (List.mem_filter.mp hi).1
  refine ⟨i,ne.1,ne.2,of_decide_eq_true (List.mem_filter.mp hi).2,?_⟩
  have opp := mul_neg_of_neg_of_pos neg mark_t
  rw [show (σ*ω i)*(σ*ω t) = (ω i*ω t)*σ^2 by ring] at opp
  by_contra! hnon
  exact (not_lt_of_ge (mul_nonneg hnon (sq_nonneg _))) opp

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
