module

public import RKCert.Dirk15NativeReverse

@[expose] public section

/-! # Conditional cubic orbit and the actual grade-four trace
The first nonlocal escape of the actual cubic reverse seed is an explicit
premise, separate from the unit escape band already deduced above it.
Once supplied, all five true powers and the clean-weight dichotomy follow. -/
namespace RKCert.Paired
open Module RKCert.OneEscape Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

abbrev reverseCubic (A : Fin 20 → Fin 20 → K) (b : Vec K 20) : Vec K 20 :=
  q₃ (transMat A) (mirror A) b

omit [CharZero K] in
theorem Order15MinimalMarkedChart.marked_four_eq (h : Order15MinimalMarkedChart A b)
    (hm : finrank K (marked A 15 4)=2) :
    marked A 15 4=markedTerminalZero (s:=19) A 15 4 := by
  symm
  exact Submodule.eq_of_le_of_finrank_eq inf_le_left
    ((h.rankTerminalZero 4 (by decide) (by decide)).trans hm.symm)

omit [CharZero K] in
theorem order15_reverseCubic_mem (ho : HasTreeOrderAtLeast A b 15)
    (T : PhysicalTerminal (s:=19) A b) :
    reverseCubic A b∈markedTerminalZero (s:=19) A 15 3 := by
  refine ⟨seed3_marked ho (by decide),prior_last_iff.mpr ?_⟩
  change (3:K)*transMat A (diag (mirror A) (diag (mirror A) b)) (Fin.last 19) -
    diag (mirror A) (diag (mirror A) (diag (mirror A) b)) (Fin.last 19)=0
  rw [T.trans_zero_terminal,diag_apply,terminal_mirror_zero T]
  ring

omit [CharZero K] in
theorem markedTerminalZero_clock {s p j : ℕ} {A : Fin (s+1) → Fin (s+1) → K}
    (hpay : j+2≤p) :
    (markedTerminalZero A p j).map (diag (mirror A)) ≤ markedTerminalZero A p (j+1) := by
  rintro _ ⟨w,hw,rfl⟩
  exact ⟨marked_clock hpay hw.1,prior_diag _ _ hw.2⟩

omit [CharZero K] in
private theorem rank_one_clock_step {s : ℕ} (T : Vec K s →ₗ[K] Vec K s)
    (U V : Submodule K (Vec K s)) (hle : U≤V) (hmap : U.map T≤V)
    (hrank : finrank K V≤finrank K U+1) (out : ¬U.map T≤U) :
    V=U⊔U.map T := by
  have hstrict : U<U⊔U.map T := lt_of_le_of_ne le_sup_left
    (fun e => out (le_sup_right.trans e.ge))
  have hh := Submodule.finrank_lt_finrank_of_lt hstrict
  symm
  exact Submodule.eq_of_le_of_finrank_le (sup_le hle hmap) (by omega)

/-- All true reverse powers at grades three to seven, conditional only on the
first (grade-three) nonlocality in the minimal marking branch. -/
theorem order15_minimal_cubic_orbit (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b)
    (hfirst : ¬ (markedTerminalZero (s:=19) A 15 3).map
      (diag (mirror A))≤markedTerminalZero (s:=19) A 15 3)
    (j : ℕ) (hl : 3≤j) (hu : j≤7) :
    markedTerminalZero (s:=19) A 15 j=chain (diag (mirror A)) ⊥ (reverseCubic A b) (j-2) := by
  let M := markedTerminalZero (s:=19) A 15
  let T := diag (mirror A)
  let τ := reverseCubic A b
  have base : M 3=chain T ⊥ τ 1 := by
    have ht : τ∈M 3 := order15_reverseCubic_mem ho h.terminal
    have hn : τ≠0 := by
      intro e
      have he := h.paid_terminal_zero 3 (by decide) (by decide)
      change M 3=twoOrbit _ _ _ _ τ 1 at he
      rw [twoOrbit,twoOrbit,h.terminal.seed1_zero,h.terminal.seed2_zero,e] at he
      simp at he
      have dd := h.rankTerminalZero 3 (by decide) (by decide)
      change finrank K (M 3)=1 at dd
      rw [he] at dd
      simp at dd
    change M 3=⊥⊔Submodule.span K ({(T^0) τ}:Set (Vec K 20))
    rw [bot_sup_eq,pow_zero,one_apply_eq_self]
    have eqRank : finrank K (M 3)=1 := h.rankTerminalZero 3 (by decide) (by decide)
    symm
    apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem ..).mpr ht)
    rw [finrank_span_singleton hn,eqRank]
  have step (k : ℕ) (hl : 3≤k) (hu : k+1≤7) : M (k+1)=M k ⊔ (M k).map T := by
    apply rank_one_clock_step T (M k) (M (k+1)) (markedTerminalZero_mono A 15 (Nat.le_succ k))
      (markedTerminalZero_clock (by omega))
    · change finrank K (M (k+1))≤finrank K (M k)+1
      rw [h.rankTerminalZero (k+1) (by omega) hu,h.rankTerminalZero k (by omega) (by omega)]
      omega
    · by_cases hk : k=3
      · subst k
        exact hfirst
      · exact order15_minimal_marked_escape ha ho h k (by omega) (by omega)
  have go (k : ℕ) (hk : k+3≤7) : M (k+3)=chain T ⊥ τ (k+1) := by
    induction k with
    | zero => exact base
    | succ k ih =>
      rw [show k+1+3=k+3+1 by omega,step (k+3) (by omega) (by omega),ih (by omega)]
      rw [chain_sup_map (by simp) (by omega : 0<k+1)]
  have ht := go (j-3) (by omega)
  rwa [show j-3+3=j by omega,show j-3+1=j-2 by omega] at ht

/-- There are at least six distinct numerical cubic-support clocks. This
counts different values, not physically repeated coordinates. -/
theorem order15_minimal_cubic_sites (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b)
    (hfirst : ¬ (markedTerminalZero (s:=19) A 15 3).map
      (diag (mirror A))≤markedTerminalZero (s:=19) A 15 3) :
    5 < (Clock.headSites (mirror A) (reverseCubic A b)).card := by
  have hh : markedTerminalZero (s:=19) A 15 7=
      chain (diag (mirror A)) ⊥ (reverseCubic A b) 5 :=
    order15_minimal_cubic_orbit ha ho h hfirst 7 (by decide) (by decide)
  apply Clock.more_sites_than_paid (F:=chain (diag (mirror A)) ⊥ (reverseCubic A b) 5)
    (fun k hk => ((chain_le_iff _).mp le_rfl).2 k hk)
  intro hz
  apply order15_minimal_marked_escape ha ho h 7 (by decide) (by decide)
  rw [hh]
  let T := diag (mirror A)
  let F := chain T ⊥ (reverseCubic A b) 5
  change F.map T≤F
  refine (le_sup_right : F.map T≤F⊔F.map T).trans ?_
  change chain T ⊥ (reverseCubic A b) 5 ⊔ (chain T ⊥ (reverseCubic A b) 5).map T≤F
  rw [chain_sup_map (by simp) (by decide : 0<5)]
  exact sup_le le_rfl ((Submodule.span_singleton_le_iff_mem ..).mpr hz)

omit [CharZero K] in
private theorem natDegree_le_of_degree_lt_succ {P : K[X]} {n : ℕ}
    (hd : P.degree<(n+1:ℕ)) : P.natDegree≤n := by
  by_cases hz : P=0
  · simp [hz]
  · have he := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hd
    omega

/-- Every visible true grade-four column has a paid quartic reverse profile
on cubic support and vanishes at every active cubic-clean row. -/
theorem order15_grade_four_profile (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b) (hm : finrank K (marked A 15 4)=2)
    (hfirst : ¬ (markedTerminalZero (s:=19) A 15 3).map
      (diag (mirror A))≤markedTerminalZero (s:=19) A 15 3)
    {v : Vec K 20} (hv : v∈zeroSpace A 4) :
    ∃ Q : K[X], Q.natDegree≤4 ∧
      (∀ i, reverseCubic A b i≠0 → v i=Q.eval (mirror A i)) ∧
      ∀ i, b i≠0 → reverseCubic A b i=0 → v i=0 := by
  have hτ := order15_reverseCubic_mem ho h.terminal
  have hp : reverseCubic A b*v∈markedTerminalZero (s:=19) A 15 7 :=
    ⟨marked_mul_tree (j:=3) (k:=4) (by decide) hτ.1 (zeroSpace_le_treeSpace A 4 hv),
      prior_last_iff.mpr (by rw [Pi.mul_apply,prior_last_iff.mp hτ.2,zero_mul])⟩
  have h7 := order15_minimal_cubic_orbit ha ho h hfirst 7 (by decide) (by decide)
  rw [h7] at hp
  obtain ⟨u,hu,Q,hQ,hEq⟩ := Clock.exists_head_poly hp
  have hUz : u=0 := by simpa using hu
  have hbf := weights_mul_zeroSpace ho (by decide : 4+1≤15) hv
  rw [h.marked_four_eq hm,order15_minimal_cubic_orbit ha ho h hfirst 4 (by decide) (by decide)] at hbf
  obtain ⟨t,ht,R,_,hR⟩ := Clock.exists_head_poly hbf
  have hTz : t=0 := by simpa using ht
  refine ⟨Q,natDegree_le_of_degree_lt_succ hQ,?_,?_⟩
  · intro i hi
    apply mul_left_cancel₀ hi
    have e := hEq i
    rw [hUz,Pi.zero_apply,zero_add,Pi.mul_apply,mul_comm (Q.eval _)] at e
    exact e
  · intro i hbi hti
    have e := hR i
    simp only [hTz,Pi.zero_apply,zero_add,Pi.mul_apply,hti,mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left hbi

end RKCert.Paired
