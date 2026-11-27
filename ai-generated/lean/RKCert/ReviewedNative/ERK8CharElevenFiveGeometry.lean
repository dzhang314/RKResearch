module

public import RKCert.ReviewedNative.ERK8CharElevenFiveEarlySentinel

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The two actual late clean roots and the seven distinct bulk
clocks in the characteristic-eleven five-off chart. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open RKResearch.Certified.Graded.ERK8CharEleven
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

def anchorRows : Finset (Fin 10) := {0,4,9}
def bulkRows : Finset (Fin 10) := Finset.univ \ anchorRows
def lastThreeRows : Finset (Fin 10) := {6,7,8}

theorem mem_bulkRows {j : Fin 10} : j∈bulkRows ↔ j≠0 ∧ j≠4 ∧ j≠9 := by
  simp [bulkRows,anchorRows]

theorem bulkRows_card : bulkRows.card=7 := by decide

noncomputable def bulkClocks (A : Matrix (Fin 10) (Fin 10) K) : Finset K :=
  bulkRows.image (nodes A)

structure FiveCleanTail (A : Matrix (Fin 10) (Fin 10) K) (x z : Fin 10) : Prop where
  x_late : x∈lastThreeRows
  z_late : z∈lastThreeRows
  xz : x<z
  x_clean : g A x=0
  z_clean : g A z=0
  clean_iff : ∀ j, g A j=0 ↔ j∈anchorRows ∨ j=x ∨ j=z
  qx : (exceptionalQuadratic : K[X]).eval (nodes A x)=0
  qz : (exceptionalQuadratic : K[X]).eval (nodes A z)=0
  clocks_ne : nodes A x≠nodes A z
  sum_one : nodes A x+nodes A z=1
  prod_eight : nodes A x*nodes A z=8

theorem lateRows_bulk {j : Fin 10} (hj : j∈lastThreeRows) : j∈bulkRows := by
  have e : j=6∨j=7∨j=8 := by simpa [lastThreeRows] using hj
  rcases e with rfl|rfl|rfl <;> decide

theorem lateRows_which {j : Fin 10} (hj : j∈lastThreeRows) : j=6 ∨ j=7 ∨ j=8 := by
  simpa [lastThreeRows] using hj

theorem anchor_clean {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {j : Fin 10} (hj : j∈anchorRows) : g A j=0 := by
  simp only [anchorRows,Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with h|h|h
  · exact h.symm ▸ S.origin_clean
  · exact h.symm ▸ S.center_clean
  · exact h.symm ▸ H.terminal_clean

theorem anchor_clock_mem {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {j : Fin 10} (hj : j∈anchorRows) : nodes A j∈({0,1,6}:Finset K) := by
  simp only [anchorRows,Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with h|h|h
  · rw [h,S.origin_clock]
    simp
  · rw [h,S.center_clock]
    simp
  · rw [h,show nodes A 9=1 from H.terminal_clock]
    simp

/-- Selector-free extraction of the two non-anchor clean stages. -/
theorem five_clean_tail_of_center_four
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    (g5 : g A 5≠0) : ∃ x z, FiveCleanTail A x z := by
  let C := (Finset.univ : Finset (Fin 10)).filter (fun j => g A j=0)
  let D := C\anchorRows
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).1
  have c : C.card=5 := by
    have n : (C.image (nodes A)).card=C.card := by
      apply Finset.card_image_iff.mpr
      intro i hi j hj e
      exact inj i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 e
    change (cleanKnots A).card=C.card at n
    omega
  have sub : anchorRows⊆C := fun j hj =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,anchor_clean H S hj⟩
  have dc : D.card=2 := by
    change (C\anchorRows).card=2
    rw [Finset.card_sdiff_of_subset sub,c,show anchorRows.card=3 by decide]
  obtain ⟨a,b,ab,e⟩ := Finset.card_eq_two.mp dc
  have ord : ∃ x z : Fin 10, x<z ∧ D={x,z} := by
    rcases lt_or_gt_of_ne ab with h|h
    · exact ⟨a,b,h,e⟩
    · exact ⟨b,a,h,e.trans (by ext j; simp only [Finset.mem_insert,Finset.mem_singleton,or_comm])⟩
  obtain ⟨x,z,xz,Dp⟩ := ord
  have xm : x∈D := by rw [Dp]; simp
  have zm : z∈D := by rw [Dp]; simp
  have xc0 : g A x=0 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp xm).1).2
  have zc0 : g A z=0 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp zm).1).2
  have roots (j : Fin 10) (hj : j∈D) : (exceptionalQuadratic : K[X]).eval (nodes A j)=0 := by
    have gj := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
    have notmem := (Finset.mem_sdiff.mp hj).2
    rcases H.clean_roots j gj with h|h|h|h
    · exact (notmem ((inj j 0 gj S.origin_clean (h.trans S.origin_clock.symm)).symm ▸ (by decide : (0:Fin 10)∈anchorRows))).elim
    · exact (notmem ((H.terminal_unique j gj h).symm ▸ (by decide : (Fin.last 9)∈anchorRows))).elim
    · exact (notmem ((inj j 4 gj S.center_clean (h.trans S.center_clock.symm)).symm ▸ (by decide : (4:Fin 10)∈anchorRows))).elim
    · exact h
  have late (j : Fin 10) (hj : j∈D) : j∈lastThreeRows := by
    have gj := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
    have notmem := (Finset.mem_sdiff.mp hj).2
    have nb := mem_bulkRows.mp (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,notmem⟩)
    have j1 : j≠1 := fun e => (high_off_before_center S (j:=1) (by decide) (by decide)) (e ▸ gj)
    have j2 : j≠2 := fun e => (high_off_before_center S (j:=2) (by decide) (by decide)) (e ▸ gj)
    have j3 : j≠3 := fun e => (high_off_before_center S (j:=3) (by decide) (by decide)) (e ▸ gj)
    have j5 : j≠5 := fun e => g5 (e ▸ gj)
    obtain ⟨j0,j4,j9⟩ := nb
    fin_cases j <;> simp_all [lastThreeRows]
  have clean_iff (j : Fin 10) : g A j=0 ↔ j∈anchorRows ∨ j=x ∨ j=z := by
    constructor
    · intro gj
      by_cases m : j∈anchorRows
      · exact Or.inl m
      · have jj : j∈D := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,gj⟩,m⟩
        rw [Dp] at jj
        exact Or.inr (by simpa using jj)
    · intro jz
      rcases jz with m|rfl|rfl
      · exact anchor_clean H S m
      · exact xc0
      · exact zc0
  have qx := roots x xm
  have qz := roots z zm
  have nc : nodes A x≠nodes A z := fun e => (ne_of_lt xz) (inj x z xc0 zc0 e)
  have sm : nodes A x+nodes A z=1 := by
    have z0 : (nodes A x-nodes A z)*(nodes A x+nodes A z-1)=0 := by
      simp only [exceptionalQuadratic_eval] at qx qz
      linear_combination qx-qz
    exact sub_eq_zero.mp ((mul_eq_zero.mp z0).resolve_left (sub_ne_zero.mpr nc))
  have pr : nodes A x*nodes A z=8 := by
    simp only [exceptionalQuadratic_eval] at qx
    linear_combination (nodes A x)*sm-qx
  exact ⟨x,z,late x xm,late z zm,xz,xc0,zc0,clean_iff,qx,qz,nc,sm,pr⟩

theorem bulk_clean_q_zero {x z : Fin 10} (T : FiveCleanTail A x z)
    {j : Fin 10} (hj : j∈bulkRows) (gj : g A j=0) :
    (exceptionalQuadratic : K[X]).eval (nodes A j)=0 := by
  rcases (T.clean_iff j).mp gj with h|h|h
  · exact ((Finset.mem_sdiff.mp hj).2 h).elim
  · exact h.symm ▸ T.qx
  · exact h.symm ▸ T.qz

theorem bulk_clock_inj (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) {x z : Fin 10} (T : FiveCleanTail A x z) :
    Set.InjOn (nodes A) (bulkRows : Set (Fin 10)) := by
  intro i hi j hj e
  have inj := order8_tag_injective_of_full_count (A:=A) (by omega)
  by_cases gi : g A i=0 <;> by_cases gj : g A j=0
  · exact inj.1 i j gi gj e
  · exact (exceptional_quadratic_ne_off H gj (e ▸ bulk_clean_q_zero T hi gi)).elim
  · exact (exceptional_quadratic_ne_off H gi (e.symm ▸ bulk_clean_q_zero T hj gj)).elim
  · exact inj.2 i j gi gj e

theorem bulkClocks_card (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) {x z : Fin 10} (T : FiveCleanTail A x z) :
    (bulkClocks A).card=7 := by
  rw [bulkClocks,Finset.card_image_iff.mpr (bulk_clock_inj five cleanFive H T),bulkRows_card]

end RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.five_clean_tail_of_center_four
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.bulk_clock_inj
