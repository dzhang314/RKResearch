module

public import RKCert.ReviewedNative.FiniteOrderedSignWindows

import Init.Data.List.Nat.Pairwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Two moments on one positive grid force two sign variations

The separator uses the first sample with sign opposite to the first
nonzero sample. Its own contribution may vanish; the earlier nonzero
sample proves strict positivity. No separator construction for arbitrary
numbers of sign runs, and no root existence principle, is required. -/
namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial SignType
open RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem triple_sublist {n : ℕ} (a : Fin n → K) {i j k : Fin n}
    (ij : i < j) (jk : j < k) : List.Sublist [a i,a j,a k] (List.ofFn a) := by
  let L := List.ofFn a
  let lift : Fin n → Fin L.length := Fin.cast (by simp [L])
  have mono : StrictMono lift := by
    intro u v uv
    change u.val < v.val
    exact uv
  have get (t : Fin n) : L[lift t] = a t := by
    simp [L, lift]
  have sorted : ([lift i,lift j,lift k] : List (Fin L.length)).Pairwise (· < ·) := by
    simp [List.pairwise_cons, mono ij, mono jk, mono (ij.trans jk)]
  have sub := List.map_getElem_sublist (l:=L) sorted
  simpa only [List.map_cons, List.map_nil, get, L] using sub

private theorem opposite_signs {a b : K} (h : a*b < 0) : sign a ≠ sign b := by
  rcases mul_neg_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [sign_pos ha,sign_neg hb]
    decide
  · rw [sign_neg ha,sign_pos hb]
    decide

private theorem two_le_variations_of_triple {n : ℕ} (a : Fin n → K) {i j k : Fin n}
    (ij : i < j) (jk : j < k) (ab : a i*a j < 0) (bc : a j*a k < 0) :
    2 ≤ (List.ofFn a).signVariations := by
  classical
  have ni : a i ≠ 0 := by intro z; rw [z, zero_mul] at ab; exact (lt_irrefl _ ab)
  have nj : a j ≠ 0 := by intro z; rw [z, zero_mul] at bc; exact (lt_irrefl _ bc)
  have nk : a k ≠ 0 := by intro z; rw [z, mul_zero] at bc; exact (lt_irrefl _ bc)
  let ss := ((List.ofFn a).map sign).filter (· ≠ 0)
  have raw := (triple_sublist a ij jk).map (sign : K → SignType)
  have sub : List.Sublist [sign (a i), sign (a j), sign (a k)] ss := by
    simpa [ss, ni, nj, nk, sign_ne_zero.mpr ni, sign_ne_zero.mpr nj, sign_ne_zero.mpr nk] using
      raw.filter (fun t : SignType => t ≠ 0)
  have chain : [sign (a i), sign (a j), sign (a k)].IsChain (· ≠ ·) := by
    exact List.isChain_cons_cons.mpr
      ⟨opposite_signs ab, List.isChain_pair.mpr (opposite_signs bc)⟩
  have hlen := List.IsChain.length_le_length_destutter_ne sub chain
  change 3 ≤ (ss.destutter (· ≠ ·)).length at hlen
  change 2 ≤ (ss.destutter (· ≠ ·)).length-1
  omega

private theorem ordered_sums_triple {n : ℕ} (a w g : Fin n → K)
    (wpos : ∀ i, 0 < w i) (mono : StrictMono g) (live : ∃ i, a i ≠ 0)
    (mass : (∑ i, w i*a i)=0) (ratioMass : (∑ i, w i*(a i*g i))=0) :
    ∃ i j k, i < j ∧ j < k ∧ a i*a j < 0 ∧ a j*a k < 0 := by
  classical
  let I := Finset.univ.filter (fun i : Fin n => a i ≠ 0)
  have ie : I.Nonempty := by
    obtain ⟨i, hi⟩ := live
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  obtain ⟨i, ii, iFirst⟩ := Finset.exists_min_image I id ie
  let q := fun k => a i*a k
  have qi : 0 < q i := mul_self_pos.mpr (Finset.mem_filter.mp ii).2
  have zm : (∑ k, w k*q k)=0 := by
    calc
      _ = a i*(∑ k, w k*a k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        dsimp [q]
        ring
      _ = 0 := by rw [mass,mul_zero]
  let J := Finset.univ.filter (fun j : Fin n => q j < 0)
  have je : J.Nonempty := by
    by_contra no
    have nonneg (k : Fin n) : 0 ≤ q k := le_of_not_gt fun bad =>
      no ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad⟩⟩
    have pos : 0 < ∑ k, w k*q k := Finset.sum_pos'
      (fun k _ => mul_nonneg (wpos k).le (nonneg k))
      ⟨i,Finset.mem_univ _,mul_pos (wpos i) qi⟩
    exact pos.ne' zm
  obtain ⟨j, jj, jFirst⟩ := Finset.exists_min_image J id je
  have qj : q j < 0 := (Finset.mem_filter.mp jj).2
  have an : a j ≠ 0 := by
    intro z
    change a i*a j < 0 at qj
    rw [z,mul_zero] at qj
    exact lt_irrefl _ qj
  have ij : i < j := lt_of_le_of_ne
    (iFirst j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,an⟩))
    (fun he => (not_lt_of_ge qi.le) (he.symm ▸ qj))
  by_contra no
  have before (k : Fin n) (kj : k < j) : 0 ≤ q k := le_of_not_gt fun bad =>
    (not_le_of_gt kj) (jFirst k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad⟩))
  have after (k : Fin n) (jk : j < k) : q k ≤ 0 := by
    apply le_of_not_gt
    intro qk
    have prod : q j*q k < 0 := mul_neg_of_neg_of_pos qj qk
    have eq : q j*q k = (a i*a i)*(a j*a k) := by dsimp [q]; ring
    have jkneg : a j*a k < 0 := by
      apply lt_of_not_ge
      intro nonneg
      rw [eq] at prod
      exact prod.not_ge (mul_nonneg qi.le nonneg)
    exact no ⟨i,j,k,ij,jk,qj,jkneg⟩
  let sep := fun k => q k*(g j-g k)
  have nonneg (k : Fin n) : 0 ≤ sep k := by
    rcases lt_trichotomy k j with kj | rfl | jk
    · exact mul_nonneg (before k kj) (sub_nonneg.mpr (mono kj).le)
    · simp [sep]
    · exact mul_nonneg_of_nonpos_of_nonpos (after k jk) (sub_nonpos.mpr (mono jk).le)
  have spos : 0 < sep i := mul_pos qi (sub_pos.mpr (mono ij))
  have pos : 0 < ∑ k, w k*sep k := Finset.sum_pos'
    (fun k _ => mul_nonneg (wpos k).le (nonneg k))
    ⟨i, Finset.mem_univ _, mul_pos (wpos i) spos⟩
  have balance : (∑ k, w k*sep k)=g j*(∑ k, w k*q k)-a i*(∑ k, w k*(a k*g k)) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [sep,q]
    ring
  have impossible : (0 : K) < 0 := by
    simpa only [balance,zm,ratioMass,mul_zero,sub_zero] using pos
  exact lt_irrefl _ impossible

/-- Reusable finite-grid statement. Neither the ratio values nor the sample
values are assumed positive; only the weights are. -/
theorem two_le_signVariations_of_ordered_sums {n : ℕ} (a w g : Fin n → K)
    (wpos : ∀ i, 0 < w i) (ratio : StrictMono g ∨ StrictAnti g) (live : ∃ i, a i ≠ 0)
    (mass : (∑ i, w i*a i)=0) (ratioMass : (∑ i, w i*(a i*g i))=0) :
    2 ≤ (List.ofFn a).signVariations := by
  have triple : ∃ i j k, i < j ∧ j < k ∧ a i*a j < 0 ∧ a j*a k < 0 := by
    rcases ratio with inc | dec
    · exact ordered_sums_triple a w g wpos inc live mass ratioMass
    · refine ordered_sums_triple a w (fun i => -g i) wpos
        (fun _ _ h => neg_lt_neg (dec h)) live mass ?_
      simp only [mul_neg,Finset.sum_neg_distrib,ratioMass,neg_zero]
  obtain ⟨i,j,k,ij,jk,ab,bc⟩ := triple
  exact two_le_variations_of_triple a ij jk ab bc

/-- Two separate zero moments with positive weights and a strictly monotone
ratio force at least two actual variations on the common exact interval grid. -/
theorem grid_variation_of_monotone_ratio {l r : K} {P U V : K[X]}
    (lr : l < r) (pn : P ≠ 0) (small : P.natDegree < 19)
    (uDegree : U.natDegree+P.natDegree ≤ 19) (vDegree : V.natDegree+P.natDegree ≤ 19)
    (_uPos : ∀ x ∈ Set.Ioo l r, 0 < U.eval x) (vPos : ∀ x ∈ Set.Ioo l r, 0 < V.eval x)
    (ratio : StrictMonoOn (fun x => U.eval x/V.eval x) (Set.Ioo l r) ∨
      StrictAntiOn (fun x => U.eval x/V.eval x) (Set.Ioo l r))
    (uZero : integral l r (U*P)=0) (vZero : integral l r (V*P)=0) :
    2 ≤ gridVariation P l r := by
  let x : Fin 19 → K := intervalPoint l r
  let a := fun i => P.eval (x i)
  let w := fun i => intervalWeight l r i*V.eval (x i)
  let g := fun i => U.eval (x i)/V.eval (x i)
  have inside (i : Fin 19) : x i ∈ Set.Ioo l r := intervalPoint_mem lr i
  have wp (i : Fin 19) : 0 < w i := mul_pos (intervalWeight_pos lr i) (vPos _ (inside i))
  have live : ∃ i, a i ≠ 0 := exists_nonzero_grid_sample lr pn small
  have vm : (∑ i, w i*a i)=0 := by
    have h := (interval_exact l r (V*P) (natDegree_mul_le.trans vDegree)).symm.trans vZero
    simpa only [w,a,x,eval_mul,mul_assoc] using h
  have um : (∑ i, w i*(a i*g i))=0 := by
    calc
      _ = ∑ i : Fin 19, intervalWeight l r i*(U*P).eval (x i) := by
        apply Finset.sum_congr rfl
        intro i _
        have vz := (vPos _ (inside i)).ne'
        dsimp only [w,a,g]
        rw [eval_mul]
        field_simp [vz]
      _ = 0 := (interval_exact l r (U*P) (natDegree_mul_le.trans uDegree)).symm.trans uZero
  have gm : StrictMono g ∨ StrictAnti g := by
    rcases ratio with h | h
    · left
      intro i j ij
      exact h (inside i) (inside j) (intervalPoint_strictMono lr ij)
    · right
      intro i j ij
      exact h (inside i) (inside j) (intervalPoint_strictMono lr ij)
  rw [gridVariation_eq]
  exact two_le_signVariations_of_ordered_sums a w g wp gm live vm um

end
end RKCert.ReviewedNative.FiniteOrderedSigns
