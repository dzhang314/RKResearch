module

public import RKCert.ReviewedNative.ERKOrderEightFourOffPhysicalRows

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The actual early off senders and first nonzero clean row

This is the upstream localization of the real four-off branch. It contains
no Lobatto scalar elimination or one-off argument.
-/
namespace RKResearch.Certified.Graded.FourOffPhysical

open RKResearch Module Polynomial Reverse OneOff ERKTaggedHorizon
open scoped Matrix Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K} {P : K[X]} {i : Fin 10}

private def zone : Finset (Fin 10) := {1,2,3,4,5}

private theorem mem_zone {k : Fin 10} : k∈zone ↔ 0<k ∧ k<6 := by
  fin_cases k <;> decide

private theorem tag_distinct_before_eight (R : RepeatAtEight A b i)
    {l k : Fin 10} (l8 : l<8) (k8 : k<8) (same : SameTag A l k) : l=k := by
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt|lt
  · exact (ne_of_lt k8) (R.unique lt same).2
  · exact (ne_of_lt l8) (R.unique lt same.symm).2

private theorem off_occurs_in_zone (D : RankData A b P) (R : RepeatAtEight A b i)
    (g6 : g A 6=0) (g7 : g A 7=0) :
    ∀ x∈offKnots A, ∃ k : Fin 10, (0:Fin 10)<k ∧ k<6 ∧ g A k≠0 ∧ nodes A k=x := by
  intro x hx
  obtain ⟨k,hk,gk,cx⟩ := R.earlierOff x hx
  have ne0 : k≠0 := fun e => gk (e.symm ▸ D.cleanZero)
  have ne6 : k≠6 := fun e => gk (e.symm ▸ g6)
  have ne7 : k≠7 := fun e => gk (e.symm ▸ g7)
  exact ⟨k,by omega,by omega,gk,cx⟩

private theorem unique_clean_in_zone (D : RankData A b P) (R : RepeatAtEight A b i)
    (g6 : g A 6=0) (g7 : g A 7=0) :
    ∃ k : Fin 10, (0:Fin 10)<k ∧ k<6 ∧ g A k=0 ∧
      (∀ j : Fin 10, 0<j → j<6 → g A j=0 → j=k) := by
  classical
  let U := zone.filter (fun k => g A k≠0)
  let T := zone.filter (fun k => g A k=0)
  have im : U.image (nodes A)=offKnots A := by
    ext x
    constructor
    · intro hx
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
      exact mem_offKnots.mpr ⟨k,(Finset.mem_filter.mp hk).2,rfl⟩
    · intro hx
      obtain ⟨k,k0,k6,kg,kc⟩ := off_occurs_in_zone D R g6 g7 x hx
      exact Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨mem_zone.mpr ⟨k0,k6⟩,kg⟩,kc⟩
  have inj : Set.InjOn (nodes A) (↑U : Set (Fin 10)) := by
    intro l hl k hk ec
    obtain ⟨lz,lg⟩ := Finset.mem_filter.mp hl
    obtain ⟨kz,kg⟩ := Finset.mem_filter.mp hk
    exact tag_distinct_before_eight R
      ((mem_zone.mp lz).2.trans (by decide : (6:Fin 10)<8))
      ((mem_zone.mp kz).2.trans (by decide : (6:Fin 10)<8))
      ⟨ec,iff_of_false lg kg⟩
  have cu : U.card=4 := by
    rw [←Finset.card_image_of_injOn inj,im,D.offCard]
  have zc : zone.card=5 := by decide
  have all : T.card+U.card=5 := by
    simpa only [T,U,zc] using (Finset.card_filter_add_card_filter_not (s:=zone) (fun k => g A k=0))
  obtain ⟨k,hT⟩ := Finset.card_eq_one.mp (by omega : T.card=1)
  have hit : k∈T := by rw [hT]; simp
  obtain ⟨kz,kg⟩ := Finset.mem_filter.mp hit
  obtain ⟨k0,k6⟩ := mem_zone.mp kz
  refine ⟨k,k0,k6,kg,?_⟩
  intro j j0 j6 jg
  have q : j∈T := Finset.mem_filter.mpr ⟨mem_zone.mpr ⟨j0,j6⟩,jg⟩
  rwa [hT,Finset.mem_singleton] at q

private theorem mat_earlier (ha : ∀ i j, i≤j → A i j=0) (v : Fin 10 → K) (k : Fin 10) :
    mat A v k = ∑ l ∈ (Finset.univ.filter (fun l : Fin 10 => l<k)), A k l*v l := by
  rw [mat_apply, Matrix.mulVec, dotProduct, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : l<k
  · simp [h]
  · simp [h,ha k l (le_of_not_gt h)]

private theorem earlier1 : (Finset.univ.filter (fun l : Fin 10 => l<1)) = {0} := by
  ext l
  fin_cases l <;> decide

private theorem earlier2 : (Finset.univ.filter (fun l : Fin 10 => l<2)) = {0,1} := by
  ext l
  fin_cases l <;> decide

private theorem earlier3 : (Finset.univ.filter (fun l : Fin 10 => l<3)) = {0,1,2} := by
  ext l
  fin_cases l <;> decide

private theorem clean_first_at_least_four (D : RankData A b P) (R : RepeatAtEight A b i)
    (ha : ∀ i j, i≤j → A i j=0) {k : Fin 10}
    (kpos : 0<k) (kg : g A k=0) (kc : nodes A k≠0)
    (early : ∀ l : Fin 10, l<k → g A l=0 → l=0) : (4:Fin 10)≤k := by
  have ag : mat A (g A) k=0 := clean_four_vanish D.bandFour kg
    (zeroSpace_mono A (by decide : 3≤4) (mat_zeroSpace_charZero A 2 (mDef_mem A 1)))
  have acg : mat A (diag (nodes A) (g A)) k=0 := clean_mixed_defect D.bandFour kg
  have ac : mat A (nodes A) k=(nodes A k)^2/2 := by
    rw [g_apply] at kg
    exact sub_eq_zero.mp kg
  apply le_of_not_gt
  intro sm
  have cases : k=1 ∨ k=2 ∨ k=3 := by omega
  rcases cases with e|e|e
  · subst k
    rw [mat_earlier ha,earlier1,Finset.sum_singleton,D.clockZero,mul_zero] at ac
    exact (div_ne_zero (pow_ne_zero 2 kc) (by norm_num)) ac.symm
  · subst k
    have go1 : g A 1≠0 := fun z => (by decide : (1:Fin 10)≠0) (early 1 (by decide) z)
    rw [mat_earlier ha,earlier2,Finset.sum_pair (by decide : (0:Fin 10)≠1),
      D.cleanZero,mul_zero,zero_add] at ag
    have a1 : A 2 1=0 := (mul_eq_zero.mp ag).resolve_right go1
    rw [mat_earlier ha,earlier2,Finset.sum_pair (by decide : (0:Fin 10)≠1),
      D.clockZero,a1,mul_zero,zero_mul,add_zero] at ac
    exact (div_ne_zero (pow_ne_zero 2 kc) (by norm_num)) ac.symm
  · subst k
    have go1 : g A 1≠0 := fun z => (by decide : (1:Fin 10)≠0) (early 1 (by decide) z)
    have go2 : g A 2≠0 := fun z => (by decide : (2:Fin 10)≠0) (early 2 (by decide) z)
    have cn : nodes A 2≠nodes A 1 := by
      intro e
      exact (by decide : (2:Fin 10)≠1) (tag_distinct_before_eight R (by decide) (by decide)
        ⟨e,iff_of_false go2 go1⟩)
    have expand (v : Fin 10 → K) :
        mat A v 3 = A 3 0*v 0+A 3 1*v 1+A 3 2*v 2 := by
      rw [mat_earlier ha,earlier3,Finset.sum_insert (by decide : (0:Fin 10)∉({1,2}:Finset (Fin 10))),
        Finset.sum_pair (by decide : (1:Fin 10)≠2)]
      ring
    rw [expand,D.cleanZero,mul_zero,zero_add] at ag
    rw [expand] at acg
    simp only [diag_apply,D.cleanZero,mul_zero,zero_add] at acg
    have z2 : (nodes A 2-nodes A 1)*(A 3 2*g A 2)=0 := by
      linear_combination acg-(nodes A 1)*ag
    have a2 : A 3 2=0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp z2).resolve_left (sub_ne_zero.mpr cn))).resolve_right go2
    rw [a2,zero_mul,add_zero] at ag
    have a1 : A 3 1=0 := (mul_eq_zero.mp ag).resolve_right go1
    rw [expand,D.clockZero,a1,a2,mul_zero,zero_mul,add_zero,zero_mul,add_zero] at ac
    exact (div_ne_zero (pow_ne_zero 2 kc) (by norm_num)) ac.symm

/-- Upstream physical placements earned on the actual matrix. The chosen
clean row is the only clean occurrence in physical indices 1 through 5.
The duplicate index is an earlier physical row; its later copy is row 8. -/
structure Placement (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10 → K)
    (P : K[X]) (i k : Fin 10) : Prop where
  rankData : RankData A b P
  repeatAtEight : RepeatAtEight A b i
  cleanSix : g A 6=0
  cleanSeven : g A 7=0
  cleanNine : g A 9=0
  firstClean : g A k=0
  firstClockNe : nodes A k≠0
  firstAtFourOrFive : k=4 ∨ k=5
  noEarlierNonzeroClean : ∀ l : Fin 10, l<k → g A l=0 → l=0
  onlyCleanInMiddle : ∀ l : Fin 10, 0<l → l<6 → g A l=0 → l=k
  offSenders : ∀ x∈offKnots A, ∃ l : Fin 10, 0<l ∧ l<6 ∧ g A l≠0 ∧ nodes A l=x

/-- No rank, positivity of individual weights, or physical row position is
a caller hypothesis. This is the intermediate producer, not an exclusion. -/
theorem physical_placement_of_order8_four_off (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 8 A b) (off : (offKnots A).card=4) :
    ∃ (P : K[X]) (i k : Fin 10), Placement A b P i k := by
  obtain ⟨P,D,i,R⟩ := rank_and_repeat_of_order8_four_off ha ho off
  have g6 := row6_clean D R ha ho
  have g7 := row7_clean D R ha
  obtain ⟨k,k0,k6,kg,single⟩ := unique_clean_in_zone D R g6 g7
  have kn : nodes A k≠0 := by
    intro e
    have d := tag_distinct_before_eight R (k6.trans (by decide : (6:Fin 10)<8))
      (by decide : (0:Fin 10)<8) (show SameTag A k 0 from ⟨e.trans D.clockZero.symm,iff_of_true kg D.cleanZero⟩)
    exact (ne_of_gt k0) d
  have early (l : Fin 10) (lk : l<k) (lg : g A l=0) : l=0 := by
    by_contra ne
    have pos : (0:Fin 10)<l := lt_of_le_of_ne (Fin.zero_le _) (fun e => ne e.symm)
    exact (ne_of_lt lk) (single l pos (lk.trans k6) lg)
  have bound := clean_first_at_least_four D R ha k0 kg kn early
  have whereK : k=4 ∨ k=5 := by omega
  exact ⟨P,i,k,D,R,g6,g7,D.cleanNine,kg,kn,whereK,early,single,off_occurs_in_zone D R g6 g7⟩

end RKResearch.Certified.Graded.FourOffPhysical
