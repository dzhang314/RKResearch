module

public import RKCert.ReviewedNative.FiniteOrderedSignWindows

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # An ordered sample polynomial cannot alternate beyond its degree

Lagrange's highest-coefficient identity is applied to one point from
each nonzero sign run. No real roots or interval grid are used. -/
namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial SignType
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def divisor {n : ℕ} (x : Fin n → K) (i : Fin n) : K :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (x i-x j)

private theorem adjacent_divisors_opp {m : ℕ} {x : Fin (m+1) → K}
    (inc : StrictMono x) (i : Fin m) :
    divisor x i.castSucc*divisor x i.succ<0 := by
  classical
  let S : Finset (Fin (m+1)) := Finset.univ
  let a := i.castSucc
  let b := i.succ
  let E := (S.erase a).erase b
  have ab : a<b := Fin.castSucc_lt_succ
  have baMem : b∈S.erase a := Finset.mem_erase.mpr ⟨ab.ne',Finset.mem_univ _⟩
  have abMem : a∈S.erase b := Finset.mem_erase.mpr ⟨ab.ne,Finset.mem_univ _⟩
  have es : (S.erase b).erase a=E := by
    ext j
    simp [E,Finset.mem_erase,and_left_comm]
  have da : divisor x a=(x a-x b)*(∏ j∈E, (x a-x j)) :=
    (Finset.mul_prod_erase (S.erase a) (fun j => x a-x j) baMem).symm
  have db : divisor x b=(x b-x a)*(∏ j∈E, (x b-x j)) := by
    rw [←es]
    exact (Finset.mul_prod_erase (S.erase b) (fun j => x b-x j) abMem).symm
  have inside : 0 < ∏ j∈E, ((x a-x j)*(x b-x j)) := by
    apply Finset.prod_pos
    intro j hj
    have ja : j≠a := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have jb : j≠b := (Finset.mem_erase.mp hj).1
    have loc : j<a ∨ b<j := by
      have va : j.val≠a.val := fun h => ja (Fin.ext h)
      have vb : j.val≠b.val := fun h => jb (Fin.ext h)
      change j.val<a.val ∨ b.val<j.val
      simp only [a,b,Fin.val_castSucc,Fin.val_succ] at *
      omega
    rcases loc with ja | bj
    · exact mul_pos (sub_pos.mpr (inc ja)) (sub_pos.mpr (inc (ja.trans ab)))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr (inc (ab.trans bj))) (sub_neg.mpr (inc bj))
  have border : (x a-x b)*(x b-x a)<0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr (inc ab)) (sub_pos.mpr (inc ab))
  change divisor x a*divisor x b<0
  calc
    _ = ((x a-x b)*(x b-x a)) * (∏ j∈E, ((x a-x j)*(x b-x j))) := by
      rw [da,db,Finset.prod_mul_distrib]
      ring
    _ < 0 := mul_neg_of_neg_of_pos border inside

/-- The degree pays for every adjacent sign reversal in a strictly ordered
family of sampled values, over an arbitrary ordered field. -/
theorem natDegree_ge_of_alternating_samples {m : ℕ} (P : K[X])
    (x : Fin (m+1) → K) (inc : StrictMono x)
    (alt : ∀ i : Fin m, P.eval (x i.castSucc)*P.eval (x i.succ)<0) :
    m≤P.natDegree := by
  classical
  by_contra no
  have short : P.natDegree<m := lt_of_not_ge no
  let q := fun i => P.eval (x i)/divisor x i
  have qp (i : Fin m) : 0 < q i.castSucc*q i.succ := by
    dsimp only [q]
    rw [div_mul_div_comm]
    exact div_pos_of_neg_of_neg (alt i) (adjacent_divisors_opp inc i)
  have eq (i : Fin m) : sign (q i.castSucc)=sign (q i.succ) := by
    rcases mul_pos_iff.mp (qp i) with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [sign_pos ha,sign_pos hb]
    · rw [sign_neg ha,sign_neg hb]
  have same (i : Fin (m+1)) : sign (q i)=sign (q 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i hi => exact (eq i).symm.trans hi
  have q0 : q 0≠0 := by
    intro z
    let i : Fin m := ⟨0,Nat.zero_lt_of_lt short⟩
    have h := qp i
    change 0<q 0*q i.succ at h
    rw [z,zero_mul] at h
    exact lt_irrefl _ h
  have signSum : sign (∑ i, q i)=sign (q 0) :=
    sign_sum Finset.univ_nonempty _ (fun i _ => same i)
  have sumNonzero : (∑ i, q i)≠0 := by
    intro z
    apply q0
    apply sign_eq_zero_iff.mp
    simpa only [z,sign_zero] using signSum.symm
  let S : Finset (Fin (m+1)) := Finset.univ
  have ds : P.natDegree<S.card := by simp [S]; omega
  have pd : P.degree<(S.card:WithBot ℕ) :=
    P.degree_le_natDegree.trans_lt (by exact_mod_cast ds)
  have h := Lagrange.coeff_eq_sum (s:=S) (v:=x) inc.injective.injOn pd
  have coeff : P.coeff m=∑ i, q i := by
    simpa [S,q,divisor] using h
  exact sumNonzero (coeff.symm.trans (coeff_eq_zero_of_natDegree_lt short))

private theorem mul_neg_of_distinct_signs {a b : K}
    (ha : sign a≠0) (hb : sign b≠0) (different : sign a≠sign b) : a*b<0 := by
  rcases lt_or_gt_of_ne (sign_ne_zero.mp ha) with an | ap <;>
    rcases lt_or_gt_of_ne (sign_ne_zero.mp hb) with bn | bp
  · exact False.elim (different ((sign_neg an).trans (sign_neg bn).symm))
  · exact mul_neg_of_neg_of_pos an bp
  · exact mul_neg_of_pos_of_neg ap bn
  · exact False.elim (different ((sign_pos ap).trans (sign_pos bp).symm))

/-- Mathlib sign changes on any strictly increasing list of samples obey
the same degree bound. Zero samples are discarded before taking sign runs. -/
theorem variation_le_natDegree (P : K[X]) (xs : List K)
    (inc : xs.Pairwise (· < ·)) : variation P xs≤P.natDegree := by
  classical
  let sg := fun x => sign (P.eval x)
  let nz := xs.filter (fun x => sg x≠0)
  let R : K → K → Prop := fun x y => sg x≠sg y
  let alt := nz.destutter R
  have f : ((xs.map P.eval).map sign).filter (· ≠ 0)=nz.map sg := by
    simp only [List.map_map,List.filter_map,nz,sg,Function.comp_def]
  have d : alt.map sg=(nz.map sg).destutter (· ≠ ·) :=
    List.map_destutter (R:=R) (l:=nz) (f:=sg) (fun _ _ _ _ => Iff.rfl)
  have count : variation P xs=alt.length-1 := by
    unfold variation List.signVariations
    rw [f,←d,List.length_map]
  rw [count]
  by_cases e : alt=[]
  · simp [e]
  let m := alt.length-1
  have nonempty : 0<alt.length := List.length_pos_iff.mpr e
  have alen : alt.length=m+1 := by dsimp only [m]; omega
  let x : Fin (m+1) → K := fun i => alt[i.val]'(by rw [alen]; exact i.isLt)
  have sub : List.Sublist alt nz := List.destutter_sublist R nz
  have altSorted : alt.Pairwise (·<·) := List.Pairwise.sublist (sub.trans List.filter_sublist) inc
  have mono : StrictMono x := by
    intro i j ij
    exact (List.pairwise_iff_getElem.mp altSorted) i.val j.val
      (by rw [alen]; exact i.isLt) (by rw [alen]; exact j.isLt) ij
  have xnz (i : Fin (m+1)) : sg (x i)≠0 := by
    have ia : x i∈alt := List.getElem_mem (by rw [alen]; exact i.isLt)
    have inz : x i∈xs.filter (fun u => sg u≠0) := sub.subset ia
    simpa using (List.mem_filter.mp inz).2
  have chain : alt.IsChain R := List.isChain_destutter R nz
  have opp (i : Fin m) : P.eval (x i.castSucc)*P.eval (x i.succ)<0 := by
    have step := (List.isChain_iff_getElem.mp chain) i.val (by rw [alen]; exact Nat.succ_lt_succ i.isLt)
    apply mul_neg_of_distinct_signs (xnz i.castSucc) (xnz i.succ)
    simpa only [R,x,Fin.val_castSucc,Fin.val_succ] using step
  exact natDegree_ge_of_alternating_samples P x mono opp

theorem HasAlternationsOn.le_natDegree {P : K[X]} {S : Set K} {m : ℕ}
    (h : HasAlternationsOn P S m) : m≤P.natDegree := by
  obtain ⟨xs, inc, _, low⟩ := h
  exact low.trans (variation_le_natDegree P xs inc)

end
end RKCert.ReviewedNative.FiniteOrderedSigns
