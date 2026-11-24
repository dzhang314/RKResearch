module

public import RKCert.Dirk15CubicBudget
public import RKCert.ChronologicalPivotProjection
public import RKCert.Dirk15NativePivots

@[expose] public section

/-! # The actual local reverse-cubic alternative
The genuine flag and pivot projection are derived from the minimal marked
chart. This file does not yet assert the weighted four-debut contradiction. -/
namespace RKCert.Paired
open Module RKCert.OneEscape PivotProjection
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

omit [CharZero K] in
theorem order15_reverseCubic_span (h : Order15CubicBudget A b) :
    markedTerminalZero (s:=19) A 15 3=Submodule.span K ({reverseCubic A b}:Set (Vec K 20)) := by
  have hq := h.paid_terminal_zero 3 (by decide) (by decide)
  change markedTerminalZero (s:=19) A 15 3=twoOrbit _ _ _ _ (reverseCubic A b) 1 at hq
  rw [hq,twoOrbit,twoOrbit,h.terminal.seed1_zero,h.terminal.seed2_zero]
  simp

/-- One numerical site for the true cubic implies a charged rank-one
chronological projection and exactly one cheap head at mark four. -/
theorem order15_local_cubic_chart (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15CubicBudget A b)
    (inv : (markedTerminalZero (s:=19) A 15 3).map (diag (mirror A))≤
      markedTerminalZero (s:=19) A 15 3) :
    ∃ (i : Fin 20) (w : Vec K 20), reverseCubic A b i≠0 ∧
      (∀ j, i<j → reverseCubic A b j=0) ∧
      (∀ j, mirror A j≠mirror A i → reverseCubic A b j=0) ∧
      ∀ j : ℕ, 3≤j → j≤6 → markedTerminalZero (s:=19) A 15 j=
        chain (diag (mirror A)) (Submodule.span K ({reverseCubic A b}:Set (Vec K 20))) w (j-3) := by
  let d := reverseCubic A b
  let U := Submodule.span K ({d}:Set (Vec K 20))
  let C' := diag (mirror A)
  let M := markedTerminalZero (s:=19) A 15
  have hU : M 3=U := order15_reverseCubic_span h
  have H (j : ℕ) (hl : 2≤j) (hu : j≤7) : finrank K (M j)=j-2 :=
    h.rankTerminalZero j hl hu
  have hn : d≠0 := by
    intro e
    have ne : finrank K U=1 := hU ▸ H 3 (by decide) (by decide)
    change finrank K (Submodule.span K ({d}:Set (Vec K 20)))=1 at ne
    rw [e,Submodule.span_zero_singleton,finrank_bot] at ne
    omega
  obtain ⟨i,hi,pref⟩ := exists_last_coordinate hn
  have hdi : d∈U := Submodule.subset_span (Set.mem_singleton d)
  have inv' : U.map C'≤U := by rw [←hU]; exact inv
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp (inv' (Submodule.mem_map_of_mem hdi))
  have hRi : r=mirror A i := by
    apply mul_right_cancel₀ hi
    have he := congrFun hr i
    simpa only [Pi.smul_apply,smul_eq_mul,diag_apply,C'] using he
  have loc (j : Fin 20) (hj : mirror A j≠mirror A i) : d j=0 := by
    have he := congrFun hr j
    simp only [Pi.smul_apply,smul_eq_mul,diag_apply,C',hRi] at he
    have zero : (mirror A j-mirror A i)*d j=0 := by rw [sub_mul,←he,sub_self]
    exact (mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr hj)
  have h34 : M 3≤M 4 := markedTerminalZero_mono A 15 (by decide)
  have not_le : ¬M 4≤M 3 := by
    intro hle
    have he := Submodule.finrank_mono hle
    rw [H 3 (by decide) (by decide),H 4 (by decide) (by decide)] at he
    omega
  obtain ⟨w,hw,hw₀⟩ := IsConcreteLE.not_le_iff_exists.mp not_le
  have h4 : M 4=chain C' U w 1 := by
    change M 4=U⊔Submodule.span K ({(C'^0) w}:Set (Vec K 20))
    rw [pow_zero,one_apply_eq_self,←hU]
    symm
    apply Submodule.eq_of_le_of_finrank_eq
      (sup_le h34 ((Submodule.span_singleton_le_iff_mem _ _).mpr hw))
    rw [Submodule.finrank_sup_span_singleton hw₀,H 3 (by decide) (by decide),
      H 4 (by decide) (by decide)]
  have step (j : ℕ) (hl : 4≤j) (hj : j+1≤6) :
      M (j+1)=M j ⊔ (M j).map C' := by
    have hle := sup_le (markedTerminalZero_mono A 15 (Nat.le_succ j))
      (markedTerminalZero_clock (by omega : j+2≤15))
    have out := order15_cubic_budget_escape ha ho h j hl (by omega)
    have Hlt : M j<M j⊔(M j).map C' := lt_of_le_of_ne le_sup_left
      (fun e => out (le_sup_right.trans e.ge))
    have hr := Submodule.finrank_lt_finrank_of_lt Hlt
    have h₁ := H j (by omega) (by omega)
    have h₂ := H (j+1) (by omega) (by omega)
    exact (Submodule.eq_of_le_of_finrank_le (show M j⊔(M j).map C'≤M (j+1) from hle)
      (by omega)).symm
  have h5 : M 5=chain C' U w 2 := by
    change M (4+1)=_
    rw [step 4 (by decide) (by decide),h4,chain_sup_map inv' (by decide)]
  have h6 : M 6=chain C' U w 3 := by
    change M (5+1)=_
    rw [step 5 (by decide) (by decide),h5,chain_sup_map inv' (by decide)]
  refine ⟨i,w,hi,pref,loc,fun j hl hu => ?_⟩
  rcases (show j=3 ∨ j=4 ∨ j=5 ∨ j=6 by omega) with rfl|rfl|rfl|rfl
  · exact hU
  · exact h4
  · exact h5
  · exact h6

end RKCert.Paired
