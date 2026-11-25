module

public import RKCert.ReviewedNative.ERK13NativePaidFrame
import RKCert.ReviewedNative.ReverseClockGain
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact marked order-13 tree ranks on original rows

This source consumes the native PaidFrame. Neither a late-terminal
assumption nor a pure head is needed for the four next clock steps.
-/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}

theorem primitiveBack_annih_marked13 (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 13 A b) (L : LastActive b (Fin.last 18))
    (seed : firstSeed A b=0) (j n : ℕ) (pay : j+n+2≤13) :
    primitiveBack A b n ≤ annih (markedTreeSpace A b j) := by
  intro v hv
  apply mem_annih.mpr
  change treeSpace A j ⊔ terminalMark A b ≤ (row v).ker
  apply sup_le (mem_annih.mp (primitiveBack_annih ho j n pay hv))
  intro x hx
  rw [terminalMark,if_pos seed] at hx
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  have vz := mem_tailZero.mp (L.primitiveBack_tail ha seed n hv) (Fin.last 18) le_rfl
  change row v (a • coordinate (Fin.last 18)) = 0
  rw [map_smul,row_coordinate,vz,smul_zero]

theorem exact_marked_reverse13 (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 13 A b) (L : LastActive b (Fin.last 18))
    (seed : firstSeed A b=0) {j : ℕ} (hi : j≤11)
    (rj : finrank K (markedTreeSpace A b j)=j+8) :
    primitiveBack A b (11-j)=annih (markedTreeSpace A b j) ∧
      finrank K (primitiveBack A b (11-j))=11-j := by
  have inc := primitiveBack_annih_marked13 ha ho L seed j (11-j) (by omega)
  have cap := finrank_annih (markedTreeSpace A b j)
  rw [Fintype.card_fin,rj] at cap
  have lo := back_finrank ha ho (11-j) (by omega)
  rw [first_dim_zero seed,zero_add] at lo
  have low := lo.trans
    (Submodule.finrank_mono (back_le_primitiveBack (A:=A) (b:=b) (11-j)))
  have upper := Submodule.finrank_mono inc
  change (j + 8) + finrank K (annih (markedTreeSpace A b j)) = 19 at cap
  have nd : finrank K (annih (markedTreeSpace A b j)) = 11-j := by
    have h : ∀ m : ℕ, j+8+m=19 → m=11-j := by omega
    exact h _ cap
  rw [nd] at upper
  have eq := Submodule.eq_of_le_of_finrank_le inc (by rwa [nd])
  exact ⟨eq,upper.antisymm low⟩

private theorem marked_five_rank13 {r : ℕ}
    {U : Submodule K (Fin 19→K)} {w : Fin 19→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativePaidHead A b r U w) (seed : firstSeed A b=0) :
    finrank K (markedTreeSpace A b 5)=12 := by
  have rank := treeSpace_rank_eq_of_separation ho (q:=5) (by decide)
    (coeff_separated ho (q:=5) (by decide))
  have out (z : firstSeed A b=0) :
      coordinate (K:=K) (Fin.last 18) ∉ treeSpace A 5 := by
    intro v
    exact endpoint_coordinate_out ha ho (q:=6) (by decide) _
      H.paidRanks.lastActive.live (H.paidRanks.lastActive.node_eq_one ha z)
      (treeSpace_mono A (by decide : 5≤6) v)
  have e := rank_sup_terminalMark (A:=A) (b:=b) (treeSpace A 5) out
  change finrank K (markedTreeSpace A b 5)=_ at e
  rw [rank,H.five,terminalDebit,if_pos seed] at e
  exact e

/-- Marked rank at grade 6 pays a two-dimensional predecessor buffer,
but the actual outgoing reverse Hermite gain is three there. -/
theorem marked_tree_next13 (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 13 A b) (L : LastActive b (Fin.last 18))
    (seed : firstSeed A b=0) {j : ℕ} (lo : 6≤j) (hi : j≤9)
    (rj : finrank K (markedTreeSpace A b j)=j+8)
    (rp : (j=6 ∧ finrank K (markedTreeSpace A b (j-1))=12) ∨
      (7≤j ∧ finrank K (markedTreeSpace A b (j-1))=j+7)) :
    markedTreeSpace A b (j+1)=
      markedTreeSpace A b j ⊔ (markedTreeSpace A b j).map (diag (nodes A)) ∧
      finrank K (markedTreeSpace A b (j+1))=j+9 := by
  let E := markedTreeSpace A b j
  let C := diag (nodes A)
  let N := 11-j
  obtain ⟨full,rN⟩ := exact_marked_reverse13 ha ho L seed (by omega : j≤11) rj
  have fresh : ¬E.map C≤E := by
    intro inv
    have yin : E≤E.comap (diag (reflectedClock A)) := by
      intro x hx
      have cx : C x∈E := inv (Submodule.mem_map_of_mem hx)
      have ex : diag (reflectedClock A) x=x-C x := by
        ext i
        simp only [C,reflectedClock,diag_apply,Pi.sub_apply,Pi.one_apply]
        ring
      change diag (reflectedClock A) x∈E
      rw [ex]
      exact E.sub_mem hx cx
    have backInv : (primitiveBack A b N).map (diag (reflectedClock A))≤
        primitiveBack A b N := by
      change (primitiveBack A b (11-j)).map (diag (reflectedClock A))≤_
      rw [full]
      exact annih_map_diag yin
    have gain := reverse_clock_invariant_gain ha ho N (by dsimp [N]; omega) backInv
    have inc := primitiveBack_annih_marked13 ha ho L seed (j-1) (N+1)
      (by dsimp [N]; omega)
    have up := Submodule.finrank_mono inc
    have cap := finrank_annih (markedTreeSpace A b (j-1))
    rw [Fintype.card_fin] at cap
    change finrank K (markedTreeSpace A b (j-1)) + finrank K (annih (markedTreeSpace A b (j-1))) = 19 at cap
    change finrank K (primitiveBack A b N)=N at rN
    rw [rN] at gain
    rcases rp with ⟨six,rp⟩ | ⟨seven,rp⟩
    · have cap7 : finrank K (annih (markedTreeSpace A b (j-1))) = 7 := by
        apply Nat.add_left_cancel (n := 12)
        simpa only [rp] using cap
      rw [cap7] at up
      exact (by dsimp [N]; omega : ¬(N+(N+2)/2 ≤ 7)) (gain.trans up)
    · have capJ : finrank K (annih (markedTreeSpace A b (j-1))) = 12-j := by
        have h : ∀ m : ℕ, j+7+m=19 → m=12-j := by omega
        exact h _ (by simpa only [rp] using cap)
      rw [capJ] at up
      exact (by dsimp [N]; omega : ¬(N+(N+2)/2 ≤ 12-j)) (gain.trans up)
  let J := E⊔E.map C
  have inc : J≤markedTreeSpace A b (j+1) := by
    apply sup_le
    · exact sup_le_sup (treeSpace_mono A (Nat.le_succ j)) le_rfl
    · change (treeSpace A j ⊔ terminalMark A b).map (diag (nodes A))≤_
      rw [Submodule.map_sup]
      exact sup_le ((Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j)).trans le_sup_left)
        ((terminalMark_clock A b).trans le_sup_right)
  have strict : E<J := lt_of_le_of_ne le_sup_left (fun eq=>fresh (le_sup_right.trans eq.ge))
  have small := Submodule.finrank_lt_finrank_of_lt strict
  have upper := marked_tree_backward_room ha ho L (j+1) (10-j) (by omega)
  rw [terminalDebit,if_pos seed] at upper
  have card := Submodule.finrank_mono inc
  change finrank K E=j+8 at rj
  exact ⟨(Submodule.eq_of_le_of_finrank_le inc (by omega)).symm,by omega⟩

theorem marked_staircase_ranks13 {r : ℕ}
    {U : Submodule K (Fin 19→K)} {w : Fin 19→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativePaidHead A b r U w) (seed : firstSeed A b=0) :
    (∀ j : ℕ, 6≤j → j≤10 → finrank K (markedTreeSpace A b j)=j+8) ∧
    (∀ j : ℕ, 6≤j → j≤9 → markedTreeSpace A b (j+1)=
      markedTreeSpace A b j ⊔ (markedTreeSpace A b j).map (diag (nodes A))) := by
  have r5 := marked_five_rank13 ha ho H seed
  have r6 := H.paidRanks.rankMid
  rw [terminalDebit,if_pos seed] at r6
  let L := H.paidRanks.lastActive
  obtain ⟨s7,r7⟩ := marked_tree_next13 ha ho L seed (j:=6)
    (by decide) (by decide) r6 (Or.inl ⟨rfl,r5⟩)
  obtain ⟨s8,r8⟩ := marked_tree_next13 ha ho L seed (j:=7)
    (by decide) (by decide) r7 (Or.inr ⟨by decide,r6⟩)
  obtain ⟨s9,r9⟩ := marked_tree_next13 ha ho L seed (j:=8)
    (by decide) (by decide) r8 (Or.inr ⟨by decide,r7⟩)
  obtain ⟨s10,r10⟩ := marked_tree_next13 ha ho L seed (j:=9)
    (by decide) (by decide) r9 (Or.inr ⟨by decide,r8⟩)
  constructor <;> intro j lo hi
  · have eq : j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
    rcases eq with rfl | rfl | rfl | rfl | rfl
    · exact r6
    · exact r7
    · exact r8
    · exact r9
    · exact r10
  · have eq : j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
    rcases eq with rfl | rfl | rfl | rfl
    · exact s7
    · exact s8
    · exact s9
    · exact s10

/-- A first degree-six polynomial alias buys the literal terminal coordinate
at true grade seven, rather than assuming an early chart. -/
theorem terminal_enters_seven_of_first_degree_six13 {G : K[X]}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (seed : firstSeed A b=0) (F : FirstEscape A b 5 G) :
    coordinate (K:=K) (Fin.last 18) ∈ treeSpace A 7 := by
  obtain ⟨d,hd,m,hm,eq⟩ := Submodule.mem_sup.mp F.paid
  rw [terminalMark,if_pos seed] at hm
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hm
  have d7 : d∈zeroSpace A 7 :=
    sup_le (zeroSpace_mono A (by decide : 6≤7))
      (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 6)) hd
  have gd : G.natDegree=6 := F.degree
  have live : a≠0 := by
    intro zero
    rw [zero,zero_smul,add_zero] at eq
    have zg := eval_eq_zero_of_coeff_separated
      (coeff_separated_next (q:=6) ha ho (by decide)) G gd.le (eq ▸ d7)
    rw [zg,natDegree_zero] at gd
    omega
  have eG : evalNodes A G∈treeSpace A 7 := evalNodes_mem_treeSpace A G (gd.le.trans (by decide))
  have scalar : a • coordinate (K:=K) (Fin.last 18) ∈ treeSpace A 7 := by
    rw [show a • coordinate (K:=K) (Fin.last 18)=evalNodes A G-d by rw [←eq]; abel]
    exact (treeSpace A 7).sub_mem eG (zeroSpace_le_treeSpace A 7 d7)
  exact ((treeSpace A 7).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr live)).mp scalar

end
end RKResearch.Certified.Graded.ERK13NativeFirst
