module

public import RKCert.ReviewedNative.ERK13NativeFirstEscape
public import RKCert.ReviewedNative.NativeFlatClockHead

import RKCert.ReviewedNative.ERKGradeFiveSurplus
public import RKCert.ReviewedNative.OddForwardBudget
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Actual paid rank and ordinary head for order thirteen

This leaf derives the raw FirstEscape input from the strictly triangular
reviewed tableau. The head is taken in ordinary, original coordinates.
There is no scalar mesh, ghost, endpoint table, or numerical sign input.
-/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}

/-- The checked grade-five surplus pays the ordinary order-13 floor 19. -/
theorem stage_floor19 {s : ℕ} {T : Matrix (Fin s) (Fin s) K} {v : Fin s → K}
    (ha : ∀ i j, i≤j → T i j=0) (ho : HasOrder 13 T v) : 19≤s := by
  have sep := coeff_separated ho (q:=6) (by decide)
  have five := grade_five_surplus_of_reviewed_order ha ho (by decide)
  have grow := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha (j:=5) sep (by decide) (by decide))
  have rank := treeSpace_rank_eq_of_separation ho (q:=6) (by decide) sep
  have room := backward_endpoint_count ha ho 6 5 (by decide) (by decide)
  change finrank K (zeroSpace T 5)<finrank K (zeroSpace T 6) at grow
  omega

theorem last_original_active (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) :
    LastActive b (Fin.last 18) := by
  refine ⟨?_,fun i hi => ((not_lt_of_ge (Fin.le_last i)) hi).elim⟩
  intro bad
  have hz (i : Fin 19) (hi : 18 ≤ i.val) : b i=0 := by
    have eq : i=Fin.last 18 := Fin.ext (by have := i.isLt; change i.val = 18; omega)
    rwa [eq]
  let len : 18≤19 := by decide
  exact (by decide : ¬(19≤18)) (stage_floor19 (prefix_strict_lower ha len)
    (prefix_hasOrder_of_suffix_zero ha ho len hz))

structure NativePaidHead (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19 → K)
    (r : ℕ) (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) : Prop where
  midpoint : OddBalancedFrame A b 6 1
  paidRanks : PaidRankInput A b
  five : finrank K (zeroSpace A 5)=5
  head : FlatClockHead A 5 1 r U w
  headBounds : 2≤r ∧ r≤5
  escapeShape : escape A b=chain (diag (nodes A)) U w (r+2)⊔terminalMark A b

theorem paid_head_of_order (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) :
    ∃ r U w, NativePaidHead A b r U w := by
  have sep := coeff_separated ho (q:=6) (by decide)
  have h5 := grade_five_surplus_of_reviewed_order ha ho (by decide)
  have grow := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha (j:=5) sep (by decide) (by decide))
  change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at grow
  have mid := odd_short_frame (q:=6) (d:=1) ha ho (by decide) (by decide) (by decide)
    (by change 6≤finrank K (zeroSpace A 6); omega)
  have f6 : finrank K (zeroSpace A 6)=6 := mid.middleDefects
  have f5 : finrank K (zeroSpace A 5)=5 := by omega
  have L := last_original_active ha ho
  obtain ⟨r,U,w,H⟩ := flat_clock_head ha (j:=5) (d:=1) sep (by decide) (by decide)
    (by change finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5)+1; omega)
  let E := zeroSpace A 6 ⊔ (zeroSpace A 6).map (diag (nodes A))
  have into : E≤zeroSpace A 7 :=
    sup_le (zeroSpace_mono A (by decide))
      (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 6))
  have e6 : zeroSpace A 6=chain (diag (nodes A)) U w (r+1) := H.flags 1 le_rfl
  have edge : E=chain (diag (nodes A)) U w (r+2) := by
    change zeroSpace A 6⊔(zeroSpace A 6).map (diag (nodes A))=_
    rw [e6,clock_chain_next H.coreStable (by omega)]
  have eR : finrank K E=7 := by
    rw [edge,show r+2=(r+1)+1 by omega,chain,←e6,
      Submodule.finrank_sup_span_singleton H.unpaid,f6]
  have emp := rank_sup_terminalMark (A:=A) (b:=b) E
    (fun _ h => last_coordinate_not_defect ho (j:=7) L (by decide) (into h))
  change finrank K (escape A b)=finrank K E+terminalDebit A b at emp
  rw [eR] at emp
  have ef := marked_defect_rank ho (j:=6) L (by decide)
  rw [f6] at ef
  have outside (z : firstSeed A b=0) :
      coordinate (K:=K) (Fin.last 18)∉treeSpace A 6 :=
    endpoint_coordinate_out ha ho (q:=6) (by decide) _ L.live (L.node_eq_one ha z)
  have markedRank := rank_sup_terminalMark (A:=A) (b:=b) (treeSpace A 6) outside
  change finrank K (markedTreeSpace A b 6)=finrank K (treeSpace A 6)+terminalDebit A b at markedRank
  have mr : finrank K (treeSpace A 6)=13 := mid.middleTree
  rw [mr] at markedRank
  have seven : finrank K (markedTreeSpace A b 7)≤14+terminalDebit A b := by
    have h := marked_tree_backward_room ha ho L 7 4 (by decide)
    omega
  have bound := clock_invariant_outgoing ha
    ((PolySeparated.of_coeff sep).mono (by decide : 5≤6)) H.coreInside H.coreStable
  change finrank K U+3≤finrank K (zeroSpace A 6) at bound
  have br := H.baseRank
  refine ⟨r,U,w,⟨mid,⟨L,markedRank,ef,emp,seven⟩,f5,H,⟨by omega,by omega⟩,?_⟩⟩
  change E⊔terminalMark A b=_
  rw [edge]

/-- The actual unmarked fork has the degree-seven first escape and the
ordinary grade-seven chart. No scalar packet has entered. -/
theorem ordinary_first_escape_of_order (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0) :
    ∃ G r U w, NativePaidHead A b r U w ∧ FirstEscape A b 6 G ∧
      treeSpace A 7=(coeffEval A 6).range⊔chain (diag (nodes A)) U w (r+2) ∧
      finrank K (treeSpace A 7)=14 :=
  by
    obtain ⟨r,U,w,H⟩ := paid_head_of_order ha ho
    obtain ⟨a,G,F⟩ := firstEscape_of_paid_rank ha ho H.paidRanks
    have a6 : a=6 := F.width.resolve_right (fun h=>seed h.2)
    subst a
    have em : escape A b=chain (diag (nodes A)) U w (r+2) := by
      simpa only [terminalMark,if_neg seed,sup_bot_eq] using H.escapeShape
    refine ⟨G,r,U,w,H,F,?_,?_⟩
    · simpa only [em,markedTreeSpace,terminalMark,if_neg seed,sup_bot_eq] using F.decomposition
    · have mark : terminalMark A b = ⊥ := by simp [terminalMark, seed]
      have debit : terminalDebit A b = 0 := by simp [terminalDebit, seed]
      have h := F.rank
      change finrank K (↥(treeSpace A 7 ⊔ terminalMark A b : Submodule K (Fin 19 → K))) = 14 + terminalDebit A b at h
      have eq : treeSpace A 7 ⊔ terminalMark A b = treeSpace A 7 := by
        rw [mark, sup_bot_eq]
      calc
        finrank K (treeSpace A 7) =
            finrank K (↥(treeSpace A 7 ⊔ terminalMark A b : Submodule K (Fin 19 → K))) :=
          congrArg (fun W : Submodule K (Fin 19 → K) => finrank K W) eq.symm
        _ = 14 := by simpa only [debit, Nat.add_zero] using h

end
end RKResearch.Certified.Graded.ERK13NativeFirst
