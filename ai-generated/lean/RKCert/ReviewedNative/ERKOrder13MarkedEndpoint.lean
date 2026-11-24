module
public import RKCert.ReviewedNative.ERKOrder13ReverseWindow
public import RKCert.ReviewedNative.ReverseLocalized

@[expose] public section

/-! # The marked order-thirteen tableau earns its full physical grade eleven -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module Polynomial RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}

private theorem forward_stable_of_reverse_stable (E : Submodule K (Fin 19→K))
    (inv : (annih E).map (diag (reflectedClock A))≤annih E) :
    E.map (diag (nodes A))≤E := by
  have h := annih_map_diag (Submodule.map_le_iff_le_comap.mp inv)
  rw [annih_annih] at h
  rintro _ ⟨x,hx,rfl⟩
  have eq : diag (nodes A) x=x-diag (reflectedClock A) x := by
    ext i
    simp [reflectedClock,sub_mul]
  rw [eq]
  exact E.sub_mem hx (h (Submodule.mem_map_of_mem hx))

variable [CharZero K]

private theorem order13_reverse_residual_paid (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder A b 13) {n : ℕ} (lo : 1≤n) (hi : n≤4) :
    normalizedResidual A b n∈back A b n := by
  obtain ⟨hb,hp,_⟩ := order13_reverse_window ha ho lo hi
  rw [hb,←hp]
  apply (primitiveBack A b n).smul_mem
  have m := monomial_mem_credit (A:=A) (b:=b) (n-1) n (by omega)
  have inc := adjointFlag_credit (A:=A) (b:=b) (monomialCredit A b) (n-1) m
  rwa [show n-1+1=n by omega] at inc

/-- At marked order thirteen, the actual first reverse line cannot be
clock-stable. The two further genuine monomial residuals are paid, so
the neutral physical two-node obstruction applies. -/
theorem order13_marked_reverse_first_escapes (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder A b 13)
    (first : firstSeed A b=0) :
    ¬(back A b 1).map (diag (reflectedClock A))≤back A b 1 := by
  have F := order13_paid_frame ha ho
  have dj (j : ℕ) (lo : 8≤j) (hi : j≤9) :
      ¬ (markedTreeSpace A b j).map (diag (nodes A))≤markedTreeSpace A b j := by
    intro inv
    have here := order13_paid_high_ranks ha ho (j:=j) (by omega) (by omega)
    have prev := order13_paid_high_ranks ha ho (j:=j-1) (by omega) (by omega)
    have d := order13_marked_debit ha ho F (by omega) (by omega) here inv
    rw [prev,here] at d
    omega
  have none (n : ℕ) (lo : 2≤n) (hi : n≤3) :
      ¬(back A b n).map (diag (reflectedClock A))≤back A b n := by
    rw [(order13_reverse_window ha ho (by omega) (by omega)).1]
    intro inv
    exact dj (11-n) (by omega) (by omega) (forward_stable_of_reverse_stable _ inv)
  exact localized_native_reverse_impossible ha ho (by decide) first
    (order13_marked_reverse_ranks ha ho first) (none 2 (by decide) (by decide))
    (none 3 (by decide) (by decide))
    (order13_reverse_residual_paid ha ho (by decide : 1≤2) (by decide))
    (order13_reverse_residual_paid ha ho (by decide : 1≤3) (by decide))

/-- The actual marked forward space at grade ten must have one more
clock direction. Since its rank is eighteen, the whole physical
19-dimensional column space is paid at grade eleven. -/
theorem order13_marked_grade_eleven (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder A b 13)
    (first : firstSeed A b=0) :
    markedTreeSpace A b 11=⊤ ∧
      markedTreeSpace A b 11=markedTreeSpace A b 10⊔(markedTreeSpace A b 10).map (diag (nodes A)) := by
  let V := markedTreeSpace A b 10
  let W := V⊔V.map (diag (nodes A))
  have dim : finrank K V=18 := by
    have h := order13_paid_high_ranks ha ho (j:=10) (by decide) (by decide)
    change finrank K V=17+terminalDebit A b at h
    rwa [show terminalDebit A b=1 by simp [terminalDebit,first]] at h
  have out : ¬V.map (diag (nodes A))≤V := by
    intro inv
    apply order13_marked_reverse_first_escapes ha ho first
    rw [(order13_reverse_window ha ho (by decide : 1≤1) (by decide)).1]
    exact marked_annih_reflected_stable inv
  have ltW : V<W := lt_of_le_of_ne le_sup_left (fun e=>out (le_sup_right.trans e.ge))
  have low := Submodule.finrank_lt_finrank_of_lt ltW
  have hi := Submodule.finrank_le (R:=K) (M:=Fin 19→K) W
  rw [Module.finrank_fin_fun] at hi
  have lower : 18<finrank K W := calc
    18 = finrank K V := dim.symm
    _ < finrank K W := low
  have rankW : finrank K W=19 := le_antisymm hi (Nat.succ_le_of_lt lower)
  have top : W=⊤ := Submodule.eq_top_of_finrank_eq (rankW.trans (Module.finrank_fin_fun K).symm)
  have inc : W≤markedTreeSpace A b 11 :=
    sup_le (sup_le_sup (treeSpace_mono A (by decide)) le_rfl) (order13_marked_clock_le A b 10)
  have full : markedTreeSpace A b 11=⊤ := top_unique (top ▸ inc)
  exact ⟨full,full.trans top.symm⟩

end
end RKResearch.Certified.Graded
