module

public import RKCert.ReviewedNative.ERK13NativePaidFrame
import RKCert.ReviewedNative.ReverseClockGain
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The original order-13 ordinary clock staircase

This file considers only the nonzero first-seed (unmarked) branch.
The three exact steps end at E10. The next Hermite gain is only one,
so neither E11 growth nor pure square payment is asserted here.
-/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}

private theorem ordinary_tree_cap (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (seed : firstSeed A b≠0) {j : ℕ} (hi : j≤11) :
    finrank K (treeSpace A j)≤j+7 := by
  have cap := backward_count ha ho j (11-j) (by omega)
  rw [first_dim_one seed] at cap
  omega

private theorem exact_reverse_at_saturation (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0) {j : ℕ} (hi : j≤11)
    (rank : finrank K (treeSpace A j)=j+7) :
    primitiveBack A b (11-j)=annih (treeSpace A j) ∧
      finrank K (primitiveBack A b (11-j))=11-j+1 := by
  have inc := primitiveBack_annih ho j (11-j) (by omega)
  have room := finrank_annih (treeSpace A j)
  rw [Fintype.card_fin,rank] at room
  have lo := back_finrank ha ho (11-j) (by omega)
  rw [first_dim_one seed] at lo
  have low := lo.trans (Submodule.finrank_mono (back_le_primitiveBack (A:=A) (b:=b) (11-j)))
  have eq := Submodule.eq_of_le_of_finrank_le inc (by omega)
  exact ⟨eq,by rw [eq]; omega⟩

/-- At grades 7,8,9, clock invariance would buy at least two reverse
dimensions, where the preceding saturated grade leaves exactly one. -/
theorem ordinary_tree_next (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0) {j : ℕ}
    (lo : 7≤j) (hi : j≤9) (rj : finrank K (treeSpace A j)=j+7)
    (rp : finrank K (treeSpace A (j-1))=j+6) :
    treeSpace A (j+1)=treeSpace A j⊔(treeSpace A j).map (diag (nodes A)) ∧
      finrank K (treeSpace A (j+1))=j+8 := by
  let E := treeSpace A j
  let C := diag (nodes A)
  let J := E⊔E.map C
  have fresh : ¬E.map C≤E := by
    intro stable
    obtain ⟨eq,rankN⟩ := exact_reverse_at_saturation ha ho seed (by omega) rj
    have yin : E≤E.comap (diag (reflectedClock A)) := by
      intro x hx
      have cx : C x∈E := stable (Submodule.mem_map_of_mem hx)
      have ex : diag (reflectedClock A) x=x-C x := by
        ext i
        simp only [C,reflectedClock,diag_apply,Pi.sub_apply,Pi.one_apply]
        ring
      change diag (reflectedClock A) x∈E
      rw [ex]
      exact E.sub_mem hx cx
    have inv : (primitiveBack A b (11-j)).map (diag (reflectedClock A))≤
        primitiveBack A b (11-j) := by
      rw [eq]
      exact annih_map_diag yin
    have gain := reverse_clock_invariant_gain ha ho (11-j) (by omega) inv
    have up := Submodule.finrank_mono
      (primitiveBack_annih ho (j-1) (11-j+1) (by omega))
    have dim := finrank_annih (treeSpace A (j-1))
    rw [Fintype.card_fin,rp] at dim
    have atLeastTwo : 2≤(11-j+2)/2 := by omega
    omega
  have inc : J≤treeSpace A (j+1) :=
    sup_le (treeSpace_mono A (Nat.le_succ j)) (Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j))
  have strict : E<J := lt_of_le_of_ne le_sup_left (fun eq=>fresh (le_sup_right.trans eq.ge))
  have small := Submodule.finrank_lt_finrank_of_lt strict
  have upper := ordinary_tree_cap ha ho seed (j:=j+1) (by omega)
  have card := Submodule.finrank_mono inc
  change finrank K E=j+7 at rj
  exact ⟨(Submodule.eq_of_le_of_finrank_le inc (by omega)).symm,by omega⟩

private theorem ordinary_chart_next {j n : ℕ} {U : Submodule K (Fin 19 → K)}
    {w : Fin 19 → K} (lo : 7≤j) (len : 0<n)
    (stable : U.map (diag (nodes A))≤U)
    (chart : treeSpace A j=(coeffEval A 6).range⊔chain (diag (nodes A)) U w n) :
    treeSpace A j⊔(treeSpace A j).map (diag (nodes A))=
      (coeffEval A 6).range⊔chain (diag (nodes A)) U w (n+1) := by
  let P := (coeffEval A 6).range
  let D := diag (nodes A)
  let H := chain D U w n
  have hm : P.map D≤treeSpace A j := by
    rintro _ ⟨v,⟨a,rfl⟩,rfl⟩
    exact treeSpace_mono A lo (diag_treeSpace A 6 (coeffEval_mem_treeSpace A 6 a))
  change treeSpace A j=P⊔H at chart
  change treeSpace A j⊔(treeSpace A j).map D=P⊔chain D U w (n+1)
  rw [chart] at hm
  rw [chart,Submodule.map_sup,← clock_chain_next stable len]
  change (P⊔H)⊔(P.map D⊔H.map D)=P⊔(H⊔H.map D)
  calc
    _ = ((P⊔H)⊔P.map D)⊔H.map D := by ac_rfl
    _ = _ := by rw [sup_eq_left.mpr hm,sup_assoc]

structure OrdinaryStaircase (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19→K)
    (G : K[X]) (r : ℕ) (U : Submodule K (Fin 19→K)) (w : Fin 19→K) : Prop where
  paidHead : NativePaidHead A b r U w
  first : FirstEscape A b 6 G
  headSeven : zeroSpace A 7=chain (diag (nodes A)) U w (r+2)
  treeSeven : treeSpace A 7=(coeffEval A 6).range⊔chain (diag (nodes A)) U w (r+2)
  treeEight : treeSpace A 8=(coeffEval A 6).range⊔chain (diag (nodes A)) U w (r+3)
  treeNine : treeSpace A 9=(coeffEval A 6).range⊔chain (diag (nodes A)) U w (r+4)
  treeTen : treeSpace A 10=(coeffEval A 6).range⊔chain (diag (nodes A)) U w (r+5)
  ranks : finrank K (treeSpace A 7)=14 ∧ finrank K (treeSpace A 8)=15 ∧
    finrank K (treeSpace A 9)=16 ∧ finrank K (treeSpace A 10)=17

theorem ordinary_staircase_of_order (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0) :
    ∃ G r U w, OrdinaryStaircase A b G r U w := by
  obtain ⟨G,r,U,w,H,F,T7,R7⟩ := ordinary_first_escape_of_order ha ho seed
  have R6 : finrank K (treeSpace A 6)=13 := H.midpoint.middleTree
  have upper := H.midpoint.nextRoom
  rw [first_dim_one seed] at upper
  change finrank K (zeroSpace A 7) + 1 ≤ 8 at upper
  have below : escape A b≤zeroSpace A 7 := by
    simpa only [markedDefectSpace,terminalMark,if_neg seed,sup_bot_eq] using escape_paid A b
  have debit : terminalDebit A b=0 := by simp [terminalDebit,seed]
  have ER := H.paidRanks.escapeRank
  rw [debit,Nat.add_zero] at ER
  have full : escape A b=zeroSpace A 7 :=
    Submodule.eq_of_le_of_finrank_le below (by change finrank K (zeroSpace A 7)≤_; omega)
  have B7 : zeroSpace A 7=chain (diag (nodes A)) U w (r+2) := by
    rw [←full,H.escapeShape,terminalMark,if_neg seed,sup_bot_eq]
  obtain ⟨s8,r8⟩ := ordinary_tree_next ha ho seed (j:=7) (by decide) (by decide) R7 R6
  have T8 := s8.trans (ordinary_chart_next (by decide) (by omega) H.head.coreStable T7)
  obtain ⟨s9,r9⟩ := ordinary_tree_next ha ho seed (j:=8) (by decide) (by decide) r8 R7
  have T9 := s9.trans (ordinary_chart_next (by decide) (by omega) H.head.coreStable T8)
  obtain ⟨s10,r10⟩ := ordinary_tree_next ha ho seed (j:=9) (by decide) (by decide) r9 r8
  have T10 := s10.trans (ordinary_chart_next (by decide) (by omega) H.head.coreStable T9)
  exact ⟨G,r,U,w,⟨H,F,B7,T7,T8,T9,T10,⟨R7,r8,r9,r10⟩⟩⟩

end
end RKResearch.Certified.Graded.ERK13NativeFirst
