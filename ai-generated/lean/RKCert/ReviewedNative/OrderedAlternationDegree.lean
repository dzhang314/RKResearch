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

/-- A list consisting of genuine nonzero values with a sign reversal at
each adjacent pair. The order of the sample points is kept separately. -/
structure AlternatingSamples (P : K[X]) (xs : List K) : Prop where
  nonzero : ∀ x∈xs, P.eval x≠0
  jumps : xs.IsChain (fun x y => P.eval x*P.eval y<0)

/-- One representative of each nonzero sign run, in the original
sample order. The empty witness is allowed when all samples vanish. -/
theorem exists_alternating_subsequence (P : K[X]) (xs : List K) :
    ∃ ys : List K, List.Sublist ys xs ∧ ys.length-1=variation P xs ∧
      AlternatingSamples P ys := by
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
  have sub : List.Sublist alt nz := List.destutter_sublist R nz
  have xnz (x : K) (hx : x∈alt) : sg x≠0 := by
    have inz : x∈xs.filter (fun u => sg u≠0) := sub.subset hx
    simpa using (List.mem_filter.mp inz).2
  have ch : alt.IsChain R := List.isChain_destutter R nz
  refine ⟨alt,sub.trans List.filter_sublist,count.symm,⟨?_,?_⟩⟩
  · intro x hx
    exact sign_ne_zero.mp (xnz x hx)
  · apply ch.imp_of_mem_imp
    intro x y hx hy hxy
    exact mul_neg_of_distinct_signs (xnz x hx) (xnz y hy) hxy

/-- Mathlib sign changes on any strictly increasing list of samples obey
the same degree bound. The witness is the extracted alternating sublist. -/
theorem variation_le_natDegree (P : K[X]) (xs : List K)
    (inc : xs.Pairwise (· < ·)) : variation P xs≤P.natDegree := by
  obtain ⟨ys,sub,count,hy⟩ := exists_alternating_subsequence P xs
  rw [←count]
  by_cases e : ys=[]
  · simp [e]
  let m := ys.length-1
  have nonempty : 0<ys.length := List.length_pos_iff.mpr e
  have alen : ys.length=m+1 := by dsimp only [m]; omega
  let x : Fin (m+1) → K := fun i => ys[i.val]'(by rw [alen]; exact i.isLt)
  have sorted : ys.Pairwise (·<·) := List.Pairwise.sublist sub inc
  have mono : StrictMono x := by
    intro i j ij
    exact (List.pairwise_iff_getElem.mp sorted) i.val j.val
      (by rw [alen]; exact i.isLt) (by rw [alen]; exact j.isLt) ij
  have opp (i : Fin m) : P.eval (x i.castSucc)*P.eval (x i.succ)<0 := by
    have step := (List.isChain_iff_getElem.mp hy.jumps) i.val
      (by rw [alen]; exact Nat.succ_lt_succ i.isLt)
    simpa only [x,Fin.val_castSucc,Fin.val_succ] using step
  exact natDegree_ge_of_alternating_samples P x mono opp

private theorem sign_ne_of_product_neg {u v : K} (h : u*v<0) :
    sign u≠sign v := by
  rcases mul_neg_iff.mp h with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [sign_pos hu,sign_neg hv]
    decide
  · rw [sign_neg hu,sign_pos hv]
    decide

/-- A genuine alternating list realizes its length minus one as the
Mathlib sign-variation count. -/
theorem AlternatingSamples.variation_eq_length {P : K[X]} {xs : List K}
    (h : AlternatingSamples P xs) : variation P xs=xs.length-1 := by
  classical
  let sg := fun x => sign (P.eval x)
  have signs : (xs.map sg).IsChain (· ≠ ·) := by
    apply (List.isChain_map sg).mpr
    exact h.jumps.imp (fun _ _ hab => sign_ne_of_product_neg hab)
  have live (v : SignType) (hv : v∈xs.map sg) : v≠0 := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    exact sign_ne_zero.mpr (h.nonzero x hx)
  have f : ((xs.map P.eval).map sign).filter (· ≠ 0)=xs.map sg := by
    rw [List.map_map]
    change (xs.map sg).filter (· ≠ 0)=xs.map sg
    exact List.filter_eq_self.mpr (fun v hv => by simp [live v hv])
  unfold variation List.signVariations
  rw [f,List.destutter_of_isChain _ _ signs,List.length_map]

/-- Recover an increasing alternating witness inside the same set. -/
theorem HasAlternationsOn.alternating_samples {P : K[X]} {S : Set K} {m : ℕ}
    (h : HasAlternationsOn P S m) :
    ∃ xs : List K, xs.Pairwise (· < ·) ∧ (∀ x∈xs, x∈S) ∧
      AlternatingSamples P xs ∧ m≤xs.length-1 := by
  obtain ⟨xs,inc,inside,low⟩ := h
  obtain ⟨ys,sub,count,hy⟩ := exists_alternating_subsequence P xs
  exact ⟨ys,List.Pairwise.sublist sub inc,fun x hx => inside x (sub.subset hx),
    hy,low.trans_eq count.symm⟩

theorem HasAlternationsOn.of_alternating_samples {P : K[X]} {S : Set K} {m : ℕ}
    {xs : List K} (inc : xs.Pairwise (· < ·)) (inside : ∀ x∈xs, x∈S)
    (h : AlternatingSamples P xs) (low : m≤xs.length-1) :
    HasAlternationsOn P S m :=
  ⟨xs,inc,inside,low.trans_eq h.variation_eq_length.symm⟩

/-- Join two sign witnesses in their given order. An unchanged sign at
the seam is dealt with by discarding the first right sample; an
opposite sign needs no deletion. Internal counts are preserved. -/
theorem AlternatingSamples.exists_join {P : K[X]} {xs ys : List K}
    (hx : AlternatingSamples P xs) (hy : AlternatingSamples P ys) :
    ∃ zs : List K, List.Sublist zs (xs++ys) ∧ AlternatingSamples P zs ∧
      (xs.length-1)+(ys.length-1)≤zs.length-1 := by
  rcases ys with _ | ⟨b, bs⟩
  · exact ⟨xs,by simp,hx,by simp⟩
  by_cases empty : xs=[]
  · subst xs
    exact ⟨b::bs,by simp,hy,by simp⟩
  let a := xs.getLast empty
  have aLive : P.eval a≠0 := hx.nonzero a (List.getLast_mem empty)
  have bLive : P.eval b≠0 := hy.nonzero b (by simp)
  have ax {u : K} (hu : u∈xs.getLast?) : u=a := by
    rw [List.getLast?_eq_some_getLast empty] at hu
    exact (Option.mem_some.mp hu).symm
  have nx : 0<xs.length := List.length_pos_iff.mpr empty
  by_cases same : sign (P.eval a)=sign (P.eval b)
  · have hc : (xs++bs).IsChain (fun x y => P.eval x*P.eval y<0) := by
      apply hx.jumps.append hy.jumps.tail
      intro u hu v hv
      have vLive := hy.nonzero v (List.mem_cons_of_mem b (List.mem_of_mem_head? hv))
      have next : P.eval b*P.eval v<0 := hy.jumps.rel_head? hv
      rw [ax hu]
      exact mul_neg_of_distinct_signs (sign_ne_zero.mpr aLive) (sign_ne_zero.mpr vLive)
        (fun h => (sign_ne_of_product_neg next) (same.symm.trans h))
    refine ⟨xs++bs,(List.Sublist.refl xs).append (List.sublist_cons_self b bs),⟨?_,hc⟩,?_⟩
    · intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hx.nonzero _ h
      · exact hy.nonzero _ (List.mem_cons_of_mem b h)
    · simp only [List.length_append,List.length_cons]
      omega
  · have hc : (xs++(b::bs)).IsChain (fun x y => P.eval x*P.eval y<0) := by
      apply hx.jumps.append hy.jumps
      intro u hu v hv
      change v∈some b at hv
      rw [ax hu,(Option.mem_some.mp hv).symm]
      exact mul_neg_of_distinct_signs (sign_ne_zero.mpr aLive) (sign_ne_zero.mpr bLive) same
    refine ⟨xs++(b::bs),List.Sublist.refl _,⟨?_,hc⟩,?_⟩
    · intro u hu
      exact (List.mem_append.mp hu).elim (hx.nonzero _) (hy.nonzero _)
    · simp only [List.length_append,List.length_cons]
      omega

/-- Variations add on strictly separated sets. The actual merged sample
list remains strictly increasing by taking a sublist of the ordered append. -/
theorem HasAlternationsOn.add_separated {P : K[X]} {S T : Set K} {m n : ℕ}
    (hS : HasAlternationsOn P S m) (hT : HasAlternationsOn P T n)
    (sep : ∀ x∈S, ∀ y∈T, x<y) : HasAlternationsOn P (S∪T) (m+n) := by
  obtain ⟨xs,xi,xS,hx,xl⟩ := hS.alternating_samples
  obtain ⟨ys,yi,yT,hy,yl⟩ := hT.alternating_samples
  obtain ⟨zs,sub,hz,low⟩ := hx.exists_join hy
  have inc : (xs++ys).Pairwise (· < ·) :=
    List.pairwise_append.mpr ⟨xi,yi,fun x hx y hy => sep x (xS x hx) y (yT y hy)⟩
  apply HasAlternationsOn.of_alternating_samples (List.Pairwise.sublist sub inc) _ hz
    ((Nat.add_le_add xl yl).trans low)
  intro z zsMem
  rcases List.mem_append.mp (sub.subset zsMem) with h | h
  · exact Or.inl (xS z h)
  · exact Or.inr (yT z h)

/-- Open windows may touch at a numeric endpoint; no endpoint sample is
counted twice. A gap between the two windows is also allowed. -/
theorem HasAlternationsOn.add_open {P : K[X]} {a b c d : K} {m n : ℕ}
    (hL : HasAlternationsOn P (Set.Ioo a b) m)
    (hR : HasAlternationsOn P (Set.Ioo c d) n)
    (ab : a≤b) (bc : b≤c) (cd : c≤d) :
    HasAlternationsOn P (Set.Ioo a d) (m+n) := by
  have joined := hL.add_separated hR (fun _ hx _ hy => hx.2.trans (bc.trans_lt hy.1))
  apply joined.mono _ le_rfl
  intro x hx
  rcases hx with h | h
  · exact ⟨h.1,h.2.trans_le (bc.trans cd)⟩
  · exact ⟨(ab.trans bc).trans_lt h.1,h.2⟩

theorem HasAlternationsOn.le_natDegree {P : K[X]} {S : Set K} {m : ℕ}
    (h : HasAlternationsOn P S m) : m≤P.natDegree := by
  obtain ⟨xs, inc, _, low⟩ := h
  exact low.trans (variation_le_natDegree P xs inc)

end
end RKCert.ReviewedNative.FiniteOrderedSigns
