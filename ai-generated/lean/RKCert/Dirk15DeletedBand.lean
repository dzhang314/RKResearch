module

public import RKCert.Dirk15MinimalChart

@[expose] public section

/-! # What terminal deletion really permits
The ordinary C extension and bilinear duality descend to the nineteen
retained coordinates. There is no projected A or order assumption. The
rank extension uses the actual clock noninvariance of the reverse spaces
as an explicit input. -/
namespace RKCert.Paired
open Module
variable {K : Type*} [Field K] {s : ℕ}

theorem deleteTerminal_diag (c v : Vec K (s+1)) :
    deleteTerminal K s (diag c v) = diag (deleteTerminal K s c) (deleteTerminal K s v) :=
  rfl

theorem coord_diag_invariance_annih {W : Submodule K (Vec K s)} {c : Vec K s}
    (h : W.map (diag c) ≤ W) : (annih W).map (diag c)≤annih W := by
  rintro _ ⟨u,hu,rfl⟩
  apply mem_annih.mpr
  intro v hv
  rw [row_flip_diag]
  exact mem_annih.mp hu _ (h (Submodule.mem_map_of_mem hv))

theorem reflected_diag_invariant_of_nodes {V : Submodule K (Vec K s)} {c : Vec K s}
    (h : V.map (diag c)≤V) : V.map (diag (1-c))≤V := by
  rintro _ ⟨v,hv,rfl⟩
  have eq : diag (1-c) v = v-diag c v := by ext i; simp [sub_mul]
  rw [eq]
  exact V.sub_mem hv (h (Submodule.mem_map_of_mem hv))

/-- A generalized terminal-deleted dual space cannot falsely appear
invariant when the actual terminal-zero marked space has a clock escape. -/
theorem deleteTerminal_dual_noninvariant (c : Vec K (s+1))
    {W : Submodule K (Vec K (s+1))} (hW : W≤prior (Fin.last s))
    (h : ¬ W.map (diag (1-c)) ≤ W) :
    ¬ (annih (W.map (deleteTerminal K s))).map (diag (deleteTerminal K s c))≤
        annih (W.map (deleteTerminal K s)) := by
  intro h'
  have he := coord_diag_invariance_annih h'
  rw [annih_annih_paired] at he
  have hC := reflected_diag_invariant_of_nodes he
  apply h
  rintro _ ⟨w,hw,rfl⟩
  have hp : diag (1-c) w∈prior (Fin.last s) := prior_diag _ _ (hW hw)
  have hD : deleteTerminal K s (diag (1-c) w)∈W.map (deleteTerminal K s) := by
    rw [deleteTerminal_diag,map_sub]
    have h1 : deleteTerminal K s (1:Vec K (s+1))=1 := rfl
    rw [h1]
    exact hC (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hw))
  obtain ⟨v,hv,heq⟩ := hD
  let z : prior (K:=K) (Fin.last s) := ⟨diag (1-c) w,hp⟩
  let t : prior (K:=K) (Fin.last s) := ⟨v,hW hv⟩
  have ee : (deleteTerminal K s).domRestrict (prior (Fin.last s)) t =
      (deleteTerminal K s).domRestrict (prior (Fin.last s)) z := heq
  have eq' := deleteTerminal_inj_on terminal_cardinal_not_prior ee
  have eqv : v = diag (1-c) w := congrArg Subtype.val eq'
  exact eqv ▸ hv

variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

abbrev deletedTreeSpace (A : Fin 20 → Fin 20 → K) (j : ℕ) :=
  (treeSpace A j).map (deleteTerminal K 19)

abbrev deletedMarkedZero (A : Fin 20 → Fin 20 → K) (j : ℕ) :=
  (markedTerminalZero (s:=19) A 15 j).map (deleteTerminal K 19)

theorem deleted_marked_rank (h : Order15MinimalMarkedChart A b) (j : ℕ) (hl : 2 ≤ j) (hu : j≤7) :
    finrank K (deletedMarkedZero A j)=j-2 := by
  have hprior : markedTerminalZero (s:=19) A 15 j≤prior (Fin.last 19) := inf_le_right
  exact (deleteTerminal_finrank (fun h => terminal_cardinal_not_prior (hprior h))).trans
    (h.rankTerminalZero j hl hu)

theorem deleted_tree_pairing (j : ℕ) (hj : j≤14) :
    deletedTreeSpace A j≤annih (deletedMarkedZero A (14-j)) := by
  rintro _ ⟨v,hv,rfl⟩
  apply mem_annih.mpr
  rintro _ ⟨w,hw,rfl⟩
  have hrow := row_after_terminal_delete (prior_last_iff.mp hw.2) (v:=v)
  rw [row_symmetric _ (deleteTerminal K 19 w),hrow]
  have hmarked : w∈annih (treeSpace A j) := by
    have he : 15-1-(14-j)=j := by omega
    have ht := hw.1
    change w∈marked A 15 (14-j) at ht
    rwa [marked,he] at ht
  exact mem_annih.mp hmarked _ hv

theorem deleted_tree_mono : Monotone (deletedTreeSpace A) :=
  fun _ _ h => Submodule.map_mono (treeSpace_mono A h)

theorem deleted_tree_clock (j : ℕ) :
    (deletedTreeSpace A j).map (diag (deleteTerminal K 19 (nodes A)))≤deletedTreeSpace A (j+1) := by
  rintro _ ⟨_,⟨v,hv,rfl⟩,rfl⟩
  rw [←deleteTerminal_diag]
  exact Submodule.mem_map_of_mem (diag_treeSpace A j hv)

theorem deleted_tree_band (h : Order15MinimalMarkedChart A b)
    (hNE : ∀ j, 4 ≤ j → j≤7 →
      ¬ (markedTerminalZero (s:=19) A 15 j).map (diag (mirror A))≤
        markedTerminalZero (s:=19) A 15 j)
    (j : ℕ) (hl : 7 ≤ j) (hu : j≤11) :
    deletedTreeSpace A j=annih (deletedMarkedZero A (14-j)) ∧
      finrank K (deletedTreeSpace A j)=j+7 := by
  have T (k : ℕ) (hk : k≤4) :
      deletedTreeSpace A (7+k)=annih (deletedMarkedZero A (14-(7+k))) ∧
        finrank K (deletedTreeSpace A (7+k))=7+k+7 := by
    induction k with
    | zero => exact ⟨h.deleted_e7_annihilator,h.deleted_e7_rank⟩
    | succ k ih =>
      obtain ⟨he,hr⟩ := ih (by omega)
      have band := hNE (14-(7+k)) (by omega) (by omega)
      let W := markedTerminalZero (s:=19) A 15 (14-(7+k))
      have hn := deleteTerminal_dual_noninvariant (nodes A) (W:=W) inf_le_right band
      change ¬ (annih (deletedMarkedZero A (14-(7+k)))).map
        (diag (deleteTerminal K 19 (nodes A)))≤annih (deletedMarkedZero A (14-(7+k))) at hn
      rw [←he] at hn
      have hi : deletedTreeSpace A (7+k)<deletedTreeSpace A (7+(k+1)) := by
        refine lt_of_le_of_ne (deleted_tree_mono (by omega)) (fun equal => hn ?_)
        have hh := deleted_tree_clock (A:=A) (7+k)
        change _≤deletedTreeSpace A (7+(k+1)) at hh
        exact hh.trans equal.ge
      have hr' := Submodule.finrank_lt_finrank_of_lt hi
      have hu := deleted_tree_pairing (A:=A) (7+(k+1)) (by omega)
      have hb := finrank_annih_eq (deletedMarkedZero A (14-(7+(k+1))))
      have hb' := deleted_marked_rank h (14-(7+(k+1))) (by omega) (by omega)
      have hh := Submodule.finrank_mono hu
      exact ⟨Submodule.eq_of_le_of_finrank_le hu (by omega),by omega⟩
  have he := T (j-7) (by omega)
  rwa [show 7+(j-7)=j by omega] at he

end RKCert.Paired
