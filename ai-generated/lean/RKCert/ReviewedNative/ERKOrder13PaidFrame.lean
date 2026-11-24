module
public import RKCert.ReviewedNative.ERKGradeFiveSurplus
public import RKCert.ReviewedNative.NativeFlatClockHead
public import RKCert.ReviewedNative.MarkedReverseDebit

@[expose] public section

/-! # Original-coordinate paid midpoint for order thirteen
No numerical signs or distinct-node assumption is used. Only the
optional terminal line is adjoined, paid by the genuine reverse flag. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- The first genuine clock escape of the short order-thirteen frame. -/
abbrev order13FirstEscape (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1)→K) :
    Submodule K (Fin (s+1)→K) :=
  (zeroSpace A 6 ⊔ (zeroSpace A 6).map (diag (nodes A))) ⊔ terminalMark A b

theorem explicit_order_thirteen_at_least_nineteen {A : Matrix (Fin s) (Fin s) K}
    {b : Fin s→K} (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b) : 19≤s := by
  have sep := coeff_separated ho (q:=6) (by decide)
  have h5 := grade_five_surplus_of_reviewed_order ha ho (by decide)
  have jump := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha (j:=5) sep (by decide) (by decide))
  change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at jump
  have rank := treeSpace_rank_eq_of_separation ho (q:=6) (by decide) sep
  have cost := backward_endpoint_count ha ho 6 5 (by decide) (by decide)
  omega

variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}

structure Order13PaidFrame (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19→K) : Prop where
  lastActive : LastActive b (Fin.last 18)
  ordinaryF5 : finrank K (zeroSpace A 5)=5
  ordinaryF6 : finrank K (zeroSpace A 6)=6
  rankPrev : finrank K (markedTreeSpace A b 5)=11+terminalDebit A b
  rankMid : finrank K (markedTreeSpace A b 6)=13+terminalDebit A b
  defectRank : finrank K (markedDefectSpace A b 6)=6+terminalDebit A b
  escapeRank : finrank K (order13FirstEscape A b)=7+terminalDebit A b
  escapePaid : order13FirstEscape A b≤markedDefectSpace A b 7
  upper : ∀ j≤11, finrank K (markedTreeSpace A b j)≤j+7+terminalDebit A b

theorem order13_last_active (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    LastActive b (Fin.last 18) := by
  refine ⟨?_,fun i hi=>((not_lt_of_ge (Fin.le_last i)) hi).elim⟩
  intro bad
  have hz (i : Fin 19) (hi : 18 ≤ i.val) : b i=0 := by
    have e : i=Fin.last 18 := Fin.ext (by have :=i.isLt; change i.val = 18; omega)
    rwa [e]
  let len : 18≤19 := by decide
  exact (by decide : ¬ (19 ≤ 18)) (explicit_order_thirteen_at_least_nineteen
    (prefix_strict_lower ha len) (prefix_hasOrder_of_suffix_zero ha ho len hz))

theorem order13_saturated_defects (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    finrank K (zeroSpace A 5)=5 ∧ finrank K (zeroSpace A 6)=6 := by
  have sep := coeff_separated ho (q:=6) (by decide)
  have h5 := grade_five_surplus_of_reviewed_order ha ho (by decide)
  have jump := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha (j:=5) sep (by decide) (by decide))
  change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at jump
  have rank := treeSpace_rank_eq_of_separation ho (q:=6) (by decide) sep
  have cost := backward_endpoint_count ha ho 6 5 (by decide) (by decide)
  omega

theorem order13_paid_frame (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    Order13PaidFrame A b := by
  have last := order13_last_active ha ho
  obtain ⟨r5,r6⟩ := order13_saturated_defects ha ho
  have sep6 := coeff_separated ho (q:=6) (by decide)
  have dim5 := treeSpace_rank_eq_of_separation ho (q:=5) (by decide)
    (coeff_separated ho (by decide))
  have dim6 := treeSpace_rank_eq_of_separation ho (q:=6) (by decide) sep6
  have outside (j : ℕ) (h : j≤6) (z : firstSeed A b=0) :
      coordinate (K:=K) (Fin.last 18)∉treeSpace A j := by
    intro hmem
    exact endpoint_coordinate_out ha ho (q:=6) (by decide) _ last.live
      (last.node_eq_one ha z) (treeSpace_mono A h hmem)
  have m5 := rank_sup_terminalMark (A:=A) (b:=b) (treeSpace A 5) (outside 5 (by decide))
  have m6 := rank_sup_terminalMark (A:=A) (b:=b) (treeSpace A 6) (outside 6 le_rfl)
  have f6 := marked_defect_rank ho (j:=6) last (by decide)
  let E := zeroSpace A 6 ⊔ (zeroSpace A 6).map (diag (nodes A))
  have low : E≤zeroSpace A 7 :=
    sup_le (zeroSpace_mono A (by decide)) (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 6))
  obtain ⟨r,U,w,H⟩ := flat_clock_head ha (j:=5) (d:=1) sep6 (by decide) (by decide)
    (by change finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5)+1; omega)
  have hh : zeroSpace A 6=chain (diag (nodes A)) U w (r+1) := H.flags 1 le_rfl
  have edge : E=chain (diag (nodes A)) U w (r+2) := by
    change zeroSpace A 6 ⊔ (zeroSpace A 6).map (diag (nodes A))=_
    rw [hh,clock_chain_next H.coreStable (by omega)]
  have rankE : finrank K E=7 := by
    rw [edge,show r+2=(r+1)+1 by omega,chain,←hh,
      Submodule.finrank_sup_span_singleton H.unpaid,r6]
  have paid := rank_sup_terminalMark (A:=A) (b:=b) E
    (fun _ h=>last_coordinate_not_defect ho (j:=7) last (by decide) (low h))
  rw [rankE] at paid
  refine ⟨last,r5,r6,?_,?_,?_,paid,sup_le_sup low le_rfl,?_⟩
  · rw [show finrank K (markedTreeSpace A b 5)=_ from m5,dim5,r5]
  · rw [show finrank K (markedTreeSpace A b 6)=_ from m6,dim6,r6]
  · rwa [r6] at f6
  · intro j hj
    have room := marked_tree_backward_room ha ho last j (11-j) (by omega)
    omega

omit [CharZero K] in
private theorem chain_with_mark {V : Type*} [AddCommGroup V] [Module K V]
    (C : V→ₗ[K] V) (U T : Submodule K V) (w : V) (n : ℕ) :
    chain C (U⊔T) w n=chain C U w n⊔T := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chain,ih]; ac_rfl

/-- The radii are measured in the intrinsic head modulo the invariant
core. The optional physical terminal is in the core, never in the head. -/
theorem order13_paid_head (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    ∃ (r : ℕ) (U : Submodule K (Fin 19→K)) (w : Fin 19→K),
      2≤r ∧ r≤5 ∧ finrank K U+r=5+terminalDebit A b ∧
      U.map (diag (nodes A))≤U ∧ U≤markedDefectSpace A b 5 ∧
      (∀ n≤1, markedDefectSpace A b (5+n)=chain (diag (nodes A)) U w (r+n)) ∧
      order13FirstEscape A b=chain (diag (nodes A)) U w (r+2) := by
  obtain ⟨r5,r6⟩ := order13_saturated_defects ha ho
  have sep6 := coeff_separated ho (q:=6) (by decide)
  obtain ⟨r,U,w,H⟩ := flat_clock_head ha (j:=5) (d:=1) sep6 (by decide) (by decide)
    (by change finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5)+1; omega)
  let T := terminalMark A b
  have last := order13_last_active ha ho
  have ur := rank_sup_terminalMark (A:=A) (b:=b) U
    (fun _ z=>last_coordinate_not_defect ho (j:=5) last (by decide) (H.coreInside z))
  have coreCost := clock_invariant_outgoing ha
    ((PolySeparated.of_coeff sep6).mono (by decide : 5≤6)) H.coreInside H.coreStable
  change finrank K U+3≤finrank K (zeroSpace A 6) at coreCost
  have rr := H.baseRank
  refine ⟨r,U⊔T,w,by omega,by omega,?_,?_,sup_le_sup H.coreInside le_rfl,?_,?_⟩
  · change finrank K (U⊔terminalMark A b : Submodule K _) + r = _
    rw [ur,Nat.add_right_comm,←rr,r5]
  · rw [Submodule.map_sup]
    exact sup_le_sup H.coreStable (terminalMark_clock A b)
  · intro n hn
    change zeroSpace A (5+n)⊔T=_
    rw [H.flags n hn,chain_with_mark]
  · change (zeroSpace A 6 ⊔ (zeroSpace A 6).map (diag (nodes A)))⊔T=_
    rw [show zeroSpace A 6=chain (diag (nodes A)) U w (r+1) from H.flags 1 le_rfl,
      clock_chain_next H.coreStable (by omega),chain_with_mark]

end
end RKResearch.Certified.Graded
