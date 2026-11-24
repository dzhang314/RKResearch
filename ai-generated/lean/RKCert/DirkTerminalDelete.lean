module

public import RKCert.Dirk15RankChart

@[expose] public section

/-! # Exact terminal-deleted pairing
This is a restriction of coordinates, not an RK method on fewer stages.
Dual transport is performed on the full original array until terminal
support and complementary rank have been checked. -/
namespace RKCert.Paired
open Module
variable {K : Type*} [Field K] {s p j : ℕ}
variable {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}

/-- The actual reverse defects that have zero physical final coordinate. -/
def markedTerminalZero (A : Fin (s+1) → Fin (s+1) → K) (p j : ℕ) :
    Submodule K (Vec K (s+1)) :=
  marked A p j ⊓ prior (Fin.last s)

theorem prior_last_iff {u : Vec K (s+1)} : u∈prior (Fin.last s) ↔ u (Fin.last s)=0 := by
  constructor
  · intro h
    exact h (Fin.last s) (Set.mem_Ici.mpr le_rfl)
  · intro h i hi
    change Fin.last s ≤ i at hi
    rwa [le_antisymm (Fin.le_last i) hi]

theorem markedTerminalZero_mono (A : Fin (s+1) → Fin (s+1) → K) (p : ℕ) :
    Monotone (markedTerminalZero A p) :=
  fun _ _ hj => inf_le_inf_right _ (marked_mono A p hj)

theorem back_sub_markedTerminalZero (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    (hT : PhysicalTerminal A b) (hj : 2 ≤ j) (hp : j+1≤p) :
    dirkBack A b (j-2)≤markedTerminalZero A p j := by
  apply le_inf (back_sub_marked ho hj hp)
  exact dirkBack_prior ha (Fin.last s) (fun i hi => (not_lt_of_ge (Fin.le_last i) hi).elim)
    (terminal_mirror_zero hT) hT.seed1_zero hT.seed2_zero _

/-- The true reverse flag cannot stall even within the terminal-zero
hyperplane once the first two primitive residuals vanish. -/
theorem markedTerminalZero_strict (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    (hT : PhysicalTerminal A b) (hj : 2 ≤ j) (hp : j+2≤p) :
    markedTerminalZero A p j < markedTerminalZero A p (j+1) := by
  refine lt_of_le_of_ne (markedTerminalZero_mono A p (show j≤j+1 from Nat.le_succ _)) ?_
  intro h
  let W := markedTerminalZero A p j
  have hq₂ : q₂ (transMat A) (mirror A) b∈W := by rw [hT.seed2_zero]; exact W.zero_mem
  have hq₃ : q₃ (transMat A) (mirror A) b∈W := by
    change q₃ (transMat A) (mirror A) b∈markedTerminalZero A p j
    rw [h]
    refine ⟨marked_mono A p (by omega : 3 ≤ j+1) (seed3_marked ho (by omega)),?_⟩
    apply prior_last_iff.mpr
    simp [q₃,hT.trans_zero_terminal,terminal_mirror_zero hT]
  have hinvN (u : Vec K (s+1)) (hu : u∈W) : transMat A u∈W := by
    change transMat A u∈markedTerminalZero A p j
    rw [h]
    exact ⟨marked_mat hp hu.1,prior_transp ha _ hu.2⟩
  have hinvY (u : Vec K (s+1)) (hu : u∈W) : diag (mirror A) u∈W := by
    change diag (mirror A) u∈markedTerminalZero A p j
    rw [h]
    exact ⟨marked_clock hp hu.1,prior_diag _ _ hu.2⟩
  have hz := mem_of_invariant_two_seeds Fin.revPerm (transMat A) _
    (causalDiag_transpose ha) (mirror A) b W hinvN hinvY hq₂ hq₃
  exact back_target_nonzero ho (by omega) (leaf_marked_zero hz.1)

theorem terminal_cardinal_annihilates {T : Submodule K (Vec K (s+1))}
    (h : T≤prior (Fin.last s)) : terminalCardinal K s∈annih T := by
  apply mem_annih.mpr
  intro v hv
  rw [row_single_left]
  exact prior_last_iff.mp (h hv)

/-- Forget the last physical slot; nothing is assumed about order after
this restriction of the numerical linear spaces. -/
def deleteTerminal (K : Type*) [Field K] (s : ℕ) : Vec K (s+1) →ₗ[K] Vec K s :=
  restrictCol Fin.castSucc

theorem deleteTerminal_apply (v : Vec K (s+1)) (j : Fin s) :
    deleteTerminal K s v j = v j.castSucc := rfl

theorem deleteTerminal_zero_iff (v : Vec K (s+1)) :
    deleteTerminal K s v=0 ↔ v=v (Fin.last s) • terminalCardinal K s := by
  classical
  constructor
  · intro h
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · have he := congrFun h j
      change v j.castSucc=0 at he
      simp [he]
  · intro h
    ext j
    have he := congrFun h j.castSucc
    simpa [deleteTerminal_apply] using he

theorem row_symmetric (u v : Vec K s) : row u v=row v u := by
  rw [row_apply,row_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem row_after_terminal_delete {u v : Vec K (s+1)} (hu : u (Fin.last s)=0) :
    row (deleteTerminal K s u) (deleteTerminal K s v)=row u v := by
  simp only [row_apply,Fin.sum_univ_castSucc,deleteTerminal_apply,hu,zero_mul,add_zero]

theorem deleteTerminal_inj_on {T : Submodule K (Vec K (s+1))}
    (hne : terminalCardinal K s∉T) :
    Function.Injective ((deleteTerminal K s).domRestrict T) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hd : deleteTerminal K s v.val=0 := hv
  rw [deleteTerminal_zero_iff] at hd
  by_cases he : v.val (Fin.last s)=0
  · apply Subtype.ext
    change v.val=0
    simpa only [he,zero_smul] using hd
  · exfalso
    apply hne
    exact (T.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr he)).mp (hd ▸ v.property)

theorem deleteTerminal_finrank {T : Submodule K (Vec K (s+1))}
    (hne : terminalCardinal K s∉T) : finrank K (T.map (deleteTerminal K s))=finrank K T := by
  rw [←LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj (deleteTerminal_inj_on hne)

theorem terminal_cardinal_not_prior : terminalCardinal K s∉prior (Fin.last s) := by
  classical
  simp [prior_last_iff]

theorem delete_after_true_annihilator {T : Submodule K (Vec K (s+1))}
    (hT : T≤prior (Fin.last s)) :
    (annih T).map (deleteTerminal K s) = annih (T.map (deleteTerminal K s)) := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    apply mem_annih.mpr
    rintro _ ⟨u,hu,rfl⟩
    rw [row_symmetric _ (deleteTerminal K s u),
      row_after_terminal_delete (prior_last_iff.mp (hT hu)),row_symmetric u v]
    exact mem_annih.mp hv u hu
  · intro w hw
    let v : Vec K (s+1) := @Fin.snoc s (fun _ => K) w 0
    have hd : deleteTerminal K s v=w := by ext i; simp [deleteTerminal_apply,v]
    refine ⟨v,?_,hd⟩
    apply mem_annih.mpr
    intro u hu
    have he := mem_annih.mp hw _ (Submodule.mem_map_of_mem hu)
    rw [←hd,row_symmetric _ (deleteTerminal K s u),
      row_after_terminal_delete (prior_last_iff.mp (hT hu)),row_symmetric u v] at he
    exact he

end RKCert.Paired
