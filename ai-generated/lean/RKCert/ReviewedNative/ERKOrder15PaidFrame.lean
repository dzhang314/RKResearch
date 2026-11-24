module
public import RKCert.ReviewedNative.ERKGradeFiveSurplus
public import RKCert.ReviewedNative.OptionalTerminalMark

@[expose] public section

/-! # The paid first forward escape of the actual explicit order-15 tableau -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module RKCert.OneEscape
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}

abbrev order15FirstEscape (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1)→K) :
    Submodule K (Fin (s+1)→K) :=
  (zeroSpace A 7 ⊔ (zeroSpace A 7).map (diag (nodes A))) ⊔ terminalMark A b

structure Order15PaidFrame (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1)→K) : Prop where
  size : s+1=22
  lastActive : LastActive b (Fin.last s)
  rankPrev : finrank K (markedTreeSpace A b 6)=13+terminalDebit A b
  rankMid : finrank K (markedTreeSpace A b 7)=15+terminalDebit A b
  defectRank : finrank K (markedDefectSpace A b 7)=7+terminalDebit A b
  escapeRank : finrank K (order15FirstEscape A b)=8+terminalDebit A b
  escapePaid : order15FirstEscape A b≤markedDefectSpace A b 8
  upper : ∀ j≤13, finrank K (markedTreeSpace A b j)≤j+8+terminalDebit A b

variable [CharZero K]

/-- At most 22 original stages forces the last coefficient to be live.
The short-prefix argument uses the real native order and actual forward
surplus, not an assumption that the last-live stage is the physical last. -/
theorem order15_short_last_active (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder A b 15) (cap : s+1≤22) : LastActive b (Fin.last s) := by
  refine ⟨?_,fun i hi=>False.elim ((not_lt_of_ge (Fin.le_last i)) hi)⟩
  intro h
  have hz (i : Fin (s+1)) (ix : s ≤ i.val) : b i=0 := by
    have e : i=Fin.last s := Fin.ext (by have :=i.isLt;change i.val=s;omega)
    rwa [e]
  have pre := prefix_hasOrder_of_suffix_zero ha ho (Nat.le_succ s) hz
  have small := (order15_ordinary_forward_head (prefix_strict_lower ha (Nat.le_succ s)) pre (by omega)).1
  omega

/-- Native paid ranks at the two physical midpoint grades. The mark
can only buy a genuine coordinate line and is never counted twice. -/
theorem order15_paid_frame (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder A b 15) (cap : s+1≤22) : Order15PaidFrame A b := by
  have last := order15_short_last_active ha ho cap
  have h5 := grade_five_surplus_of_reviewed_order ha ho (by decide)
  have sep := coeff_separated ho (q:=7) (by decide)
  have ht5 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha (j:=5) sep (by decide) (by decide))
  have ht6 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha (j:=6) sep (by decide) (by decide))
  change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at ht5
  change finrank K (zeroSpace A 6)<finrank K (zeroSpace A 7) at ht6
  have forward : 7≤finrank K (zeroSpace A 7) := by omega
  have S := odd_short_frame ha ho (q:=7) (d:=1) (by decide) (by decide) (by omega) (by
    change 7≤finrank K (zeroSpace A 7)
    exact forward)
  have r7 : finrank K (zeroSpace A 7)=7 := S.middleDefects
  have r6 : finrank K (zeroSpace A 6)=6 := by omega
  have dim6 := treeSpace_rank_eq_of_separation ho (q:=6) (by decide)
    (coeff_separated ho (by decide))
  have un (j : ℕ) (h : j≤7) (z : firstSeed A b=0) :
      coordinate (K:=K) (Fin.last s)∉treeSpace A j := by
    intro e
    exact endpoint_coordinate_out ha ho (q:=7) (by decide) _ last.live (last.node_eq_one ha z)
      (treeSpace_mono A h e)
  have mark6 := rank_sup_terminalMark (treeSpace A 6) (un 6 (by decide))
  have mark7 := rank_sup_terminalMark (treeSpace A 7) (un 7 (by decide))
  have defect := marked_defect_rank ho (j:=7) last (by decide)
  have low : zeroSpace A 7 ⊔ (zeroSpace A 7).map (diag (nodes A))≤zeroSpace A 8 :=
    sup_le (zeroSpace_mono A (by decide)) (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 7))
  obtain ⟨size,r,U,w,_,_,_,_,_,_,_,edge,_⟩:=order15_ordinary_forward_head ha ho cap
  have paid := rank_sup_terminalMark (A:=A) (b:=b) (zeroSpace A 7 ⊔ (zeroSpace A 7).map (diag (nodes A)))
    (fun _ h=>last_coordinate_not_defect ho (j:=8) last (by decide) (low h))
  rw [edge] at paid
  have sz : s+1=22 := size
  have mid : finrank K (treeSpace A 7)=15 := S.middleTree
  refine ⟨sz,last,?_,?_,?_,paid,sup_le_sup low le_rfl,?_⟩
  · change finrank K (markedTreeSpace A b 6)=_ at mark6
    omega
  · change finrank K (markedTreeSpace A b 7)=_ at mark7
    omega
  · omega
  · intro j jh
    have r := marked_tree_backward_room ha ho last j (13-j) (by omega)
    omega

omit [CharZero K] in
private theorem chain_add_terminal_core {V : Type*} [AddCommGroup V] [Module K V]
    (C : V→ₗ[K] V) (U T : Submodule K V) (w : V) (n : ℕ) :
    chain C (U⊔T) w n=chain C U w n⊔T := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chain,ih]; ac_rfl

/-- The ordinary physical head is retained after paying a single terminal
coordinate in its invariant core. No node ordering or positivity is used. -/
theorem order15_paid_head (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder A b 15) (cap : s+1≤22) :
    ∃ (r : ℕ) (U : Submodule K (Fin (s+1)→K)) (w : Fin (s+1)→K),
      2≤r ∧ finrank K U+r=5+terminalDebit A b ∧ U.map (diag (nodes A))≤U ∧
      U≤markedDefectSpace A b 5 ∧
      (∀ n≤2, markedDefectSpace A b (5+n)=chain (diag (nodes A)) U w (r+n)) ∧
      order15FirstEscape A b=chain (diag (nodes A)) U w (r+3) := by
  obtain ⟨_,r,U,w,rr,rank,stable,core,_,h,edge,_,_⟩:=order15_ordinary_forward_head ha ho cap
  let T := terminalMark A b
  have last := order15_short_last_active ha ho cap
  have ur := rank_sup_terminalMark (A:=A) (b:=b) U
    (fun _ z=>last_coordinate_not_defect ho (j:=5) last (by decide) (core z))
  refine ⟨r,U⊔T,w,rr,by change finrank K (U⊔terminalMark A b : Submodule K _) + r = _;omega,
    ?_,sup_le_sup core le_rfl,?_,?_⟩
  · rw [Submodule.map_sup]
    exact sup_le_sup stable (terminalMark_clock A b)
  · intro n hn
    change zeroSpace A (5+n)⊔T=_
    rw [h n hn,chain_add_terminal_core]
  · change (zeroSpace A 7 ⊔ (zeroSpace A 7).map (diag (nodes A)))⊔T=_
    rw [edge,chain_add_terminal_core]

end
end RKResearch.Certified.Graded
