module

public import RKCert.Dirk15ReverseNonlocal

@[expose] public section

/-! # Actual reverse cubic orbit and clean Radau ports, before exclusion -/
namespace RKCert.Paired
open Module RKCert.OneEscape
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

theorem order15_cubic_budget_orbit (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15CubicBudget A b) (j : ℕ) (hl : 3≤j) (hu : j≤7) :
    markedTerminalZero (s:=19) A 15 j=chain (diag (mirror A)) ⊥ (reverseCubic A b) (j-2) := by
  let M := markedTerminalZero (s:=19) A 15
  let T := diag (mirror A)
  let τ := reverseCubic A b
  have base : M 3=chain T ⊥ τ 1 := by
    change M 3=⊥⊔Submodule.span K ({(T^0) τ}:Set (Vec K 20))
    rw [pow_zero,Module.End.one_eq_id,LinearMap.id_apply,bot_sup_eq]
    exact order15_reverseCubic_span h
  have step (k : ℕ) (hl : 3≤k) (hu : k+1≤7) : M (k+1)=M k ⊔ (M k).map T := by
    have hle : M k⊔(M k).map T≤M (k+1) :=
      sup_le (markedTerminalZero_mono A 15 (Nat.le_succ k)) (markedTerminalZero_clock (by omega))
    have out : ¬(M k).map T≤M k := by
      by_cases he : k=3
      · subst k
        exact order15_cubic_budget_nonlocal ha ho h
      · exact order15_cubic_budget_escape ha ho h k (by omega) (by omega)
    have hs : M k<M k⊔(M k).map T := lt_of_le_of_ne le_sup_left
      (fun he => out (le_sup_right.trans he.ge))
    have hr := Submodule.finrank_lt_finrank_of_lt hs
    have e1 : finrank K (M k)=k-2 := h.rankTerminalZero k (by omega) (by omega)
    have e2 : finrank K (M (k+1))=k+1-2 := h.rankTerminalZero (k+1) (by omega) (by omega)
    exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm
  have go (k : ℕ) (hk : k+3≤7) : M (k+3)=chain T ⊥ τ (k+1) := by
    induction k with
    | zero => exact base
    | succ k ih =>
      rw [show k+1+3=k+3+1 by omega,step (k+3) (by omega) (by omega),ih (by omega)]
      rw [chain_sup_map (by simp) (by omega : 0<k+1)]
  have ht := go (j-3) (by omega)
  rwa [show j-3+3=j by omega,show j-3+1=j-2 by omega] at ht

/-- The entire non-C(2) full marked band, with no additional mark-invariance
or nodal hypothesis. The theorem still assumes the hypothetical p15 method. -/
theorem order15_nonC2_reverse_orbit (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15NonC2Chart A b) (j : ℕ) (hl : 3≤j) (hu : j≤7) :
    marked A 15 j=chain (diag (mirror A)) ⊥ (reverseCubic A b) (j-2) := by
  rw [h.marked_terminal_zero ha ho j (by omega) hu]
  exact order15_cubic_budget_orbit ha ho (h.cubic_budget ha ho) j hl hu

/-- Every b-active cubic-clean physical slot in the non-C(2) boundary is
a genuine left-Radau port, not merely a slot assumed to have this property. -/
theorem order15_nonC2_tau_clean_radau (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0)
    (i : Fin 20) (hbi : b i≠0) (hti : reverseCubic A b i=0) :
    mirror A i=0 ∨ (radauLeft7 : Polynomial K).eval (mirror A i)=0 := by
  have h := order15_nonC2_rank_chart ha ho hq
  apply nonC2_radau_port ho h i hbi
  intro w hw
  rw [order15_nonC2_reverse_orbit ha ho h 7 (by decide) (by decide)] at hw
  obtain ⟨u,hu,Q,_,he⟩ := Clock.exists_head_poly hw
  have hu0 : u=0 := by simpa using hu
  simpa only [hu0,Pi.zero_apply,hti,mul_zero,add_zero] using he i

end RKCert.Paired
