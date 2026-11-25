module

public import RKCert.ReviewedNative.FiniteStoppedBracket

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Two-site stopped bracket for a literal four-cut factorization

This is the reflected right-side bracket after one real mark has been
erased. Four known unit factors and the one uncounted outside factor
make the exact sign fit, so no sign variation sampling is needed. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerChronology

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.RightPoleInterpolation
open RKCert.ReviewedNative.FiniteStoppedBracket

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
set_option maxHeartbeats 1200000

private theorem cut_split (xs : List K) {t : K} (live : ∀ x ∈ xs, x≠t) :
    ∃ L R : List K, (∀ x ∈ L, x < t) ∧ (∀ x ∈ R, t < x) ∧
      L.length+R.length=xs.length ∧ cutProduct xs=cutProduct L*cutProduct R := by
  induction xs with
  | nil => exact ⟨[],[],by simp,by simp,by simp,by simp⟩
  | cons a xs ih =>
      obtain ⟨L,R,toLeft,toRight,len,prod⟩ :=
        ih (fun x hx => live x (List.mem_cons_of_mem _ hx))
      by_cases h : a < t
      · refine ⟨a::L,R,?_,toRight,?_,?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hh
          · exact h
          · exact toLeft x hh
        · simp only [List.length_cons]
          omega
        · simp only [cutProduct_cons,prod]
          ring
      · have h' : t < a := lt_of_le_of_ne (le_of_not_gt h) (live a (by simp)).symm
        refine ⟨L,a::R,toLeft,?_,?_,?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hh
          · exact h'
          · exact toRight x hh
        · simp only [List.length_cons]
          omega
        · simp only [cutProduct_cons,prod]
          ring

private theorem cuts_nonzero (xs : List K) : cutProduct xs ≠ 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cutProduct_cons]
    exact mul_ne_zero (X_sub_C_ne_zero x) ih

private theorem cuts_positive (xs : List K) (x : K) (hx : ∀ z ∈ xs, z < x) :
    0 < (cutProduct xs).eval x := by
  induction xs with
  | nil => simp
  | cons z xs ih =>
    simp only [cutProduct_cons,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos (sub_pos.mpr (hx z (by simp))) (ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)))

private theorem outer_linear_degree (b : K) : (C b-X : K[X]).natDegree≤1 :=
  (natDegree_sub_le _ _).trans (by simp)

private theorem outer_linear_nonzero (b : K) : (C b-X : K[X])≠0 := by
  rw [show (C b-X : K[X])=-(X-C b) by ring]
  exact neg_ne_zero.mpr (X_sub_C_ne_zero b)

/-- The parity is exactly that of the right-side cuts. The exterior
factor is positive on both integration meshes. -/
private theorem separator_of_actual_cuts {P : K[X]} {b t : K} {xs L R : List K}
    (b1 : 1 < b) (t0 : 0 < t) (t1 : t < 1)
    (factor : P=(C b-X)*cutProduct xs) (split : cutProduct xs=cutProduct L*cutProduct R)
    (l : ∀ x ∈ L,x < t) (r : ∀ x ∈ R,t < x) :
    StopSeparator P 0 t 1 ((-1 : K)^R.length) L R := by
  let τ : K := (-1 : K)^R.length
  have ev (x : K) : P.eval x = (b-x)*((cutProduct L).eval x*(cutProduct R).eval x) := by
    simp only [factor,split,eval_mul,eval_sub,eval_C,eval_X]
  have parity : τ*((-1 : K)^R.length)=1 := by
    dsimp [τ]
    rw [←mul_pow]
    norm_num
  refine ⟨l,r,?_,?_⟩
  · intro i live
    let x := intervalPoint (0 : K) t i
    have xt : x < t := (intervalPoint_mem t0 i).2
    have bp : 0 < b-x := sub_pos.mpr (xt.trans (t1.trans b1))
    have rp := poleProduct_pos R x (fun a ha => xt.trans (r a ha))
    rw [poleProduct_orientation] at rp
    have ln : (cutProduct L).eval x≠0 := by
      intro z
      apply live
      change P.eval x=0
      rw [ev,z,zero_mul,mul_zero]
    change 0 < τ*P.eval x*(cutProduct L).eval x
    rw [ev]
    calc
      0 < ((b-x)*(τ*(cutProduct R).eval x))*((cutProduct L).eval x)^2 :=
        mul_pos (mul_pos bp rp) (sq_pos_of_ne_zero ln)
      _ = _ := by ring
  · intro i live
    let x := intervalPoint t (1 : K) i
    have tx : t < x := (intervalPoint_mem t1 i).1
    have bp : 0 < b-x := sub_pos.mpr ((intervalPoint_mem t1 i).2.trans b1)
    have lp := cuts_positive L x (fun a ha => (l a ha).trans tx)
    have rn : (cutProduct R).eval x≠0 := by
      intro z
      apply live
      change P.eval x=0
      rw [ev,z,mul_zero,mul_zero]
    change 0 < (τ*((-1 : K)^R.length))*P.eval x*(cutProduct R).eval x
    rw [parity,one_mul,ev]
    calc
      0 < ((b-x)*(cutProduct L).eval x)*((cutProduct R).eval x)^2 :=
        mul_pos (mul_pos bp lp) (sq_pos_of_ne_zero rn)
      _ = _ := by ring

/-- Exact two-term receipt at a reflected stop. The one retained
off-stop atom is forced strictly to the left and has opposite signed
mass. Degree bookkeeping is literal: local 6, bracket 6 of 7, total
14 of 19, and a nonzero survivor from degree at most 5+1. -/
theorem two_node_paid_left {a b t s mt ms : K} {P : K[X]}
    (a0 : a < 0) (b1 : 1 < b) (xs : List K) (xs4 : xs.length=4)
    (factor : P=(C b-X)*cutProduct xs) (live : ∀ x ∈ xs,x≠t)
    (ht : t∈Set.Ioo (0 : K) 1) (hs : s∈Set.Ioo (0 : K) 1) (st : s≠t)
    (law : ∀ F : K[X], F.natDegree≤7 →
      integral 0 1 (X*poleProduct [(1 : K),1-a]*P*F) = ms*F.eval s+mt*F.eval t)
    (localZero : integral 0 t (X*P)=0) :
    s < t ∧ ms*mt < 0 := by
  obtain ⟨L,R,hL,hR,lr,split⟩ := cut_split xs live
  let D : List K := [1,1-a]
  let A : K[X] := X
  let H := poleProduct D
  let τ : K := (-1)^R.length
  let ls := if s < t then [s] else []
  let rs := if s < t then [] else [s]
  let μ (x : K) := if x=t then mt else ms
  have sep : StopSeparator P 0 t 1 τ L R := separator_of_actual_cuts b1 ht.1 ht.2 factor split hL hR
  have poles (x : K) (hx : x∈D) : 1≤x := by
    simp [D] at hx
    rcases hx with rfl | rfl
    · exact le_rfl
    · linarith only [a0]
  have Hshape : H=(C (1 : K)-X)*(C (1-a)-X) := by simp [H,D,poleProduct]
  have hd : H.natDegree ≤ 2 := by
    rw [Hshape]
    exact natDegree_mul_le_of_le (outer_linear_degree 1) (outer_linear_degree (1-a))
  have pd : P.natDegree≤5 := by
    rw [factor]
    have earn := natDegree_mul_le_of_le (outer_linear_degree b) (cutProduct_degree xs)
    rw [xs4] at earn
    exact earn
  have pn : P≠0 := by
    rw [factor]
    exact mul_ne_zero (outer_linear_nonzero b) (cuts_nonzero xs)
  have oneSide : ls.length+rs.length=1 := by by_cases h : s < t <;> simp [ls,rs,h]
  have cost : bracketDegree L R ls rs=6 := by
    unfold bracketDegree
    omega
  have lsLt (x : K) (hx : x∈ls) : x < t := by
    by_cases h : s < t
    · have eq : x=s := by simpa [ls,h] using hx
      simpa only [eq] using h
    · simp [ls,h] at hx
  have rsGt (x : K) (hx : x∈rs) : t < x := by
    by_cases h : s < t
    · simp [rs,h] at hx
    · have eq : x=s := by simpa [rs,h] using hx
      have liveS : t < s := lt_of_le_of_ne (le_of_not_gt h) st.symm
      simpa only [eq] using liveS
  have localDeg : (A*P).natDegree≤19 :=
    (natDegree_mul_le_of_le natDegree_X.le pd).trans (by decide)
  have grid14 : A.natDegree+H.natDegree+P.natDegree+bracketDegree L R ls rs≤14 := by
    have ad : A.natDegree=1 := natDegree_X
    omega
  have law' (F : K[X]) (fd : F.natDegree≤7) :
      integral 0 1 (A*H*P*F) =
        atomSum ls μ F.eval + μ t*F.eval t + atomSum rs μ F.eval := by
    change integral 0 1 (X*poleProduct [(1 : K),1-a]*P*F) = _
    rw [law F fd]
    by_cases h : s < t <;> simp [ls,rs,h,μ,st,atomSum,add_comm]
  have br := strict_bracket_of_pole_grid (A:=A) (P:=P) (μ:=μ) (b:=7)
    ht.1 ht.2 D L R ls rs (by simp [D]) poles sep lsLt rsGt
    (fun i => by simpa only [A,eval_X] using (intervalPoint_mem ht.1 i).1)
    (fun i => by simpa only [A,eval_X] using (ht.1.trans (intervalPoint_mem ht.2 i).1).le)
    pn (by omega) localDeg (by omega) (grid14.trans (by decide)) law' localZero
  change τ*atomSum ls μ (fun x => (H.eval x)⁻¹) < 0 ∧
    0 < τ*(atomSum ls μ (fun x => (H.eval x)⁻¹)+μ t*(H.eval t)⁻¹) at br
  by_cases h : s < t
  · have neg : τ*(ms*(H.eval s)⁻¹) < 0 := by simpa [ls,h,μ,st,atomSum] using br.1
    have plus : 0 < τ*(ms*(H.eval s)⁻¹+mt*(H.eval t)⁻¹) := by simpa [ls,h,μ,st,atomSum] using br.2
    have pos : 0 < τ*(mt*(H.eval t)⁻¹) := by
      rw [mul_add] at plus
      linarith only [neg,plus]
    have sInv : 0 < (H.eval s)⁻¹ :=
      inv_pos.mpr (poleProduct_pos D s (fun x hx => hs.2.trans_le (poles x hx)))
    have tInv : 0 < (H.eval t)⁻¹ :=
      inv_pos.mpr (poleProduct_pos D t (fun x hx => ht.2.trans_le (poles x hx)))
    have sign := mul_neg_of_neg_of_pos neg pos
    have e : (τ*(ms*(H.eval s)⁻¹))*(τ*(mt*(H.eval t)⁻¹)) =
        (τ^2*(H.eval s)⁻¹*(H.eval t)⁻¹)*(ms*mt) := by ring
    rw [e] at sign
    exact ⟨h,neg_of_mul_neg_right sign (mul_nonneg (mul_nonneg (sq_nonneg _) sInv.le) tInv.le)⟩
  · have bad : (0 : K) < 0 := by simpa [ls,h,atomSum] using br.1
    exact (lt_irrefl _ bad).elim

end
end RKCert.ReviewedNative.WeakFiveSoleInnerChronology
