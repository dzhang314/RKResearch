module

public import RKCert.DirkTerminalDelete

@[expose] public section

/-! # The two actual anchored marking alternatives at p=15 -/
namespace RKCert.Paired
open Module
variable {K : Type*} [Field K] {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

structure Order15AnchoredChart (A : Fin 20 → Fin 20 → K) (b : Vec K 20) : Prop where
  first_zero : ∀ j, A 0 j=0
  last_weight : b (Fin.last 19)≠0
  f3 : finrank K (zeroSpace A 3)=1
  f6 : finrank K (zeroSpace A 6)=5
  f7 : finrank K (zeroSpace A 7)=6
  e7 : finrank K (treeSpace A 7)=14

theorem order15_anchored_rank_chart [CharZero K]
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1=0) : Order15AnchoredChart A b := by
  obtain ⟨h₃,h₆,h₇,e₇⟩ := dirk_chart15_origin_of_grade6 ha ho hq
    (dirk_grade_six_surplus ha ho (by decide))
  exact ⟨dirk_first_row ha hq,terminal_weight_from_native ha ho,h₃,h₆,h₇,e₇⟩

structure Order15MinimalMarkedChart (A : Fin 20 → Fin 20 → K) (b : Vec K 20) : Prop where
  initial : Order15AnchoredChart A b
  terminal : PhysicalTerminal (s:=19) A b
  terminal_not_mem : terminalCardinal K 19∉treeSpace A 7
  paid_terminal_zero : ∀ j : ℕ, 2 ≤ j → j≤7 →
    markedTerminalZero (s:=19) A 15 j=dirkBack A b (j-2)
  rankTerminalZero : ∀ j : ℕ, 2 ≤ j → j≤7 →
    finrank K (markedTerminalZero (s:=19) A 15 j)=j-2
  f4_terminal_zero : ∀ w∈zeroSpace A 4, w (Fin.last 19)=0
  add_actual_terminal :
    annih (markedTerminalZero (s:=19) A 15 7) =
      treeSpace A 7 ⊔ Submodule.span K ({terminalCardinal K 19} : Set (Vec K 20))
  deleted_e7_rank : finrank K ((treeSpace A 7).map (deleteTerminal K 19))=14
  deleted_e7_annihilator :
    (treeSpace A 7).map (deleteTerminal K 19) =
      annih ((markedTerminalZero (s:=19) A 15 7).map (deleteTerminal K 19))

/-- The minimal marking branch. Equality identifies the exact paid
terminal-zero orbit, without assuming a normalization of transpose or order
of the terminal-deleted array. -/
theorem order15_minimal_marked_chart [CharZero K]
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1=0)
    (hm : finrank K (marked A 15 4)=2) : Order15MinimalMarkedChart A b := by
  have ini := order15_anchored_rank_chart ha ho hq
  have h23 := Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=2) (by decide) (by decide))
  have h34 := Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=3) (by decide) (by decide))
  change finrank K (marked A 15 2)<finrank K (marked A 15 3) at h23
  change finrank K (marked A 15 3)<finrank K (marked A 15 4) at h34
  have M₂ : marked A 15 2=⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have h1 := marked_mono A 15 (by decide : 1≤2) (seed1_marked ho (by decide))
  have h2 := seed2_marked ho (by decide)
  rw [M₂] at h1 h2
  have h₁ : backSeed1 A b=0 := by simpa using h1
  have h₂ : q₂ (transMat A) (mirror A) b=0 := by simpa using h2
  let T := terminal_diag_from_seeds ha ini.last_weight h₁ h₂
  have notCard := first_row_anchored_terminal_not_mem ho (m:=7) (by decide) T ini.first_zero
  let M : ℕ → Submodule K (Vec K 20) := markedTerminalZero (s:=19) A 15
  have M7_lt : M 7 < marked A 15 7 := by
    refine lt_of_le_of_ne inf_le_left (fun e => notCard ?_)
    have hl : M 7≤prior (Fin.last 19) := inf_le_right
    rw [e] at hl
    have hz := terminal_cardinal_annihilates hl
    rwa [marked,annih_annih_paired] at hz
  have upper7 : finrank K (M 7)≤5 := by
    have e := Submodule.finrank_lt_finrank_of_lt M7_lt
    have h := marked_rank A 15 7
    change finrank K (treeSpace A 7)+finrank K (marked A 15 7)=20 at h
    have := ini.e7
    omega
  have bound (j n : ℕ) (hl : 2 ≤ j) (hu : j+n≤7) :
      finrank K (M j)+n≤finrank K (M (j+n)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := ih (by omega)
      have h' := Submodule.finrank_lt_finrank_of_lt
        (markedTerminalZero_strict ha ho T (j:=j+n) (by omega) (by omega))
      change finrank K (M (j+n))<finrank K (M (j+n+1)) at h'
      rw [show j+(n+1)=j+n+1 by omega]
      omega
  have eqRank (j : ℕ) (hl : 2 ≤ j) (hu : j≤7) : finrank K (M j)=j-2 := by
    have h := bound j (7-j) hl (by omega)
    rw [Nat.add_sub_of_le hu] at h
    have hc := Submodule.finrank_mono (back_sub_markedTerminalZero ha ho T hl (by omega : j+1≤15))
    have hb := dirkBack_rank ha ho (j-2) (by omega)
    change finrank K (dirkBack A b (j-2))≤finrank K (M j) at hc
    omega
  have eqBack (j : ℕ) (hl : 2 ≤ j) (hu : j≤7) : M j=dirkBack A b (j-2) := by
    have hle := back_sub_markedTerminalZero ha ho T hl (by omega : j+1≤15)
    have hB := dirkBack_rank ha ho (j-2) (by omega)
    have eh := eqRank j hl hu
    symm
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)
  have M4eq : M 4=marked A 15 4 :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left ((eqRank 4 (by decide) (by decide)).trans hm.symm)
  have f4_zero (w : Vec K 20) (hw : w∈zeroSpace A 4) : w (Fin.last 19)=0 := by
    have hx := weights_mul_zeroSpace ho (by decide : 4+1≤15) hw
    rw [←M4eq] at hx
    have h := prior_last_iff.mp hx.2
    exact (mul_eq_zero.mp h).resolve_left T.weight_ne
  let ec := terminalCardinal K 19
  have E_le : treeSpace A 7≤annih (M 7) := by
    apply annih_flip_le
    change M 7≤marked A 15 7
    exact inf_le_left
  have Te := terminal_cardinal_annihilates (T:=M 7) inf_le_right
  have E_eq : annih (M 7)=treeSpace A 7 ⊔ Submodule.span K ({ec}:Set (Vec K 20)) := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq (sup_le E_le ((Submodule.span_singleton_le_iff_mem _ _).mpr Te))
    rw [Submodule.finrank_sup_span_singleton notCard]
    have hd := finrank_annih_eq (M 7)
    change finrank K (M 7)+finrank K (annih (M 7))=20 at hd
    have hh : finrank K (M 7)=5 := eqRank 7 (by decide) (by decide)
    rw [ini.e7]
    omega
  have D_same : (annih (M 7)).map (deleteTerminal K 19)=(treeSpace A 7).map (deleteTerminal K 19) := by
    rw [E_eq,Submodule.map_sup,Submodule.map_span]
    have h0 : deleteTerminal K 19 ec=0 := by
      ext i
      rw [deleteTerminal_apply,Pi.zero_apply]
      exact terminalCardinal_apply_ne (Fin.castSucc_ne_last i)
    simp [Set.image_singleton,h0]
  refine ⟨ini,T,notCard,eqBack,eqRank,f4_zero,E_eq,?_,?_⟩
  · exact (deleteTerminal_finrank notCard).trans ini.e7
  · rw [←D_same]
    exact delete_after_true_annihilator (T:=M 7) inf_le_right

/-- The complementary early-surplus branch saturates the full marked flag;
this theorem does not assume a terminal row in that branch. -/
theorem order15_early_marked_ranks [CharZero K]
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1=0)
    (hm : 3≤finrank K (marked A 15 4)) {j : ℕ} (h₄ : 4 ≤ j) (h₇ : j≤7) :
    finrank K (marked A 15 j)=j-1 := by
  have ini := order15_anchored_rank_chart ha ho hq
  have h45 := Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=4) (by decide) (by decide))
  have h56 := Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=5) (by decide) (by decide))
  have h67 := Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=6) (by decide) (by decide))
  change finrank K (marked A 15 4)<finrank K (marked A 15 5) at h45
  change finrank K (marked A 15 5)<finrank K (marked A 15 6) at h56
  change finrank K (marked A 15 6)<finrank K (marked A 15 7) at h67
  have h := marked_rank A 15 7
  change finrank K (treeSpace A 7)+finrank K (marked A 15 7)=20 at h
  have := ini.e7
  rcases (show j=4 ∨ j=5 ∨ j=6 ∨ j=7 by omega) with rfl|rfl|rfl|rfl <;>
    norm_num <;> omega

end RKCert.Paired
