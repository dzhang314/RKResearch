module

public import RKCert.Dirk15CubicOrbit

@[expose] public section

/-! # The simultaneous physical ghost kernel in the anchored minimal branch
The support characterization is pointwise. A spectral statement alone does
not delete rows and there is no first-row assumption for the non-C(2) chart. -/
namespace RKCert.Paired
open Module RKCert.OneEscape Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

noncomputable def simultaneousGhosts (A : Fin 20 → Fin 20 → K) (b : Vec K 20) :
    Submodule K (Vec K 20) :=
  (LinearMap.ker (LinearMap.proj 0)) ⊓
    ⨅ (i : Fin 20) (_ : b i≠0 ∨ reverseCubic A b i≠0), LinearMap.ker (LinearMap.proj i)

omit [CharZero K] in
theorem simultaneousGhosts_mem {v : Vec K 20} :
    v∈simultaneousGhosts A b ↔ v 0=0 ∧
      ∀ i : Fin 20, (b i≠0 ∨ reverseCubic A b i≠0) → v i=0 := by
  simp [simultaneousGhosts]

omit [CharZero K] in
theorem simultaneousGhosts_invariant :
    (simultaneousGhosts A b).map (diag (nodes A))≤simultaneousGhosts A b := by
  rintro _ ⟨v,hv,rfl⟩
  change v∈simultaneousGhosts A b at hv
  rw [simultaneousGhosts_mem] at hv ⊢
  refine ⟨by simp [hv.1],?_⟩
  intro i hi
  simp [hv.2 i hi]

omit [CharZero K] in
theorem simultaneousGhosts_mul_closed :
    Clock.MulClosed (simultaneousGhosts A b) := by
  intro v hv w _
  rw [simultaneousGhosts_mem] at hv ⊢
  refine ⟨by simp [hv.1],?_⟩
  intro i hi
  simp [hv.2 i hi]

omit [CharZero K] in
/-- The true terminal-deleted ordinary annihilator, augmented by the zero
origin and true zero weighted probes, contributes no new pure direction. -/
theorem anchored_deleted_annihilator_pure (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b) {v : Vec K 20}
    (hv : v∈annih (markedTerminalZero (s:=19) A 15 7))
    (h0 : v 0=0) (hb : ∀ i, b i*v i=0) : v∈zeroSpace A 7 := by
  classical
  rw [h.add_actual_terminal] at hv
  obtain ⟨z,hz,t,ht,e⟩ := Submodule.mem_sup.mp hv
  obtain ⟨κ,eqt⟩ := Submodule.mem_span_singleton.mp ht
  subst t
  obtain ⟨a,hf⟩ := exists_poly_zeroSpace ho (by decide : 7+1≤15) hz
  have ec0 : terminalCardinal K 19 0=0 := terminalCardinal_apply_ne (by decide)
  have hz0 : z 0=0 := by
    have he := congrFun e 0
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,ec0,mul_zero,add_zero,h0] using he
  have ha0 : a 0=0 := by
    have hfirst : (z-polyEval A 7 a) 0=0 := zeroSpace_first_of_row h.initial.first_zero 7 hf
    simpa only [Pi.sub_apply,hz0,polyEval_first_of_row h.initial.first_zero,zero_sub,neg_eq_zero]
      using hfirst
  have hvp (k : ℕ) : probe A b k v=0 := by
    simp only [probe,row_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [mul_right_comm,hb i,zero_mul]
  have ep (k : Fin 8) : probe A b k.val (polyEval A 7 a) = -(κ*b (Fin.last 19)) := by
    have hz' := congrArg (probe A b k.val) e
    have hn : probe A b k.val (terminalCardinal K 19)=b (Fin.last 19) := by
      change row (fun i => b i*(nodes A i)^k.val) (Pi.single (Fin.last 19) 1)=_
      rw [row_single_right]
      simp only [h.terminal.node_one,one_pow,mul_one]
    have hp := probe_zeroSpace ho (by have := k.isLt; omega : k.val+7+1≤15) hf
    change probe A b k.val (z-polyEval A 7 a)=0 at hp
    rw [map_sub,sub_eq_zero] at hp
    rw [map_add,hp,map_smul,smul_eq_mul,hn,hvp] at hz'
    exact eq_neg_of_add_eq_zero_left hz'
  have hκ : κ=0 := by
    have he := constant_moments_origin_zero ho (by decide) a ha0 _ ep
    exact (mul_eq_zero.mp (neg_eq_zero.mp he)).resolve_right h.terminal.weight_ne
  have az : a=0 := by
    funext j
    apply moments_detect ho (d:=1) (by decide) (by decide) (fun i l => by omega) a _ j
    intro i
    have hi := ep i
    rw [hκ,zero_mul,neg_zero,probe_polyEval ho (by have := i.isLt; omega)] at hi
    exact hi
  rw [az,map_zero,sub_zero] at hf
  rw [hκ,zero_smul,add_zero] at e
  exact e ▸ hf

/-- The full physical simultaneous ghost-coordinate space is contained in
the true ordinary F7 once the first reverse-clock escape is established. -/
theorem order15_simultaneous_ghosts_le (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b)
    (hfirst : ¬(markedTerminalZero (s:=19) A 15 3).map
      (diag (mirror A))≤markedTerminalZero (s:=19) A 15 3) :
    simultaneousGhosts A b≤zeroSpace A 7 := by
  intro v hv
  rw [simultaneousGhosts_mem] at hv
  refine anchored_deleted_annihilator_pure ho h ?_ hv.1 ?_
  · apply mem_annih.mpr
    intro w hw
    rw [order15_minimal_cubic_orbit ha ho h hfirst 7 (by decide) (by decide)] at hw
    obtain ⟨u,hu,Q,_,hw⟩ := Clock.exists_head_poly hw
    have hu0 : u=0 := by simpa using hu
    rw [row_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases ht : reverseCubic A b i=0
    · simp [hw i,hu0,ht]
    · simp [hv.2 i (Or.inr ht)]
  · intro i
    by_cases hbi : b i=0
    · simp [hbi]
    · simp [hv.2 i (Or.inl hbi)]

end RKCert.Paired
