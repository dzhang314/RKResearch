module
public import RKCert.ReviewedNative.ERKOrder13Staircase

@[expose] public section

/-! # Native exact reverse row spaces from the actual paid order-thirteen bands -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}

/-- Neither flag may be replaced by a smaller projected space. Both
ordinary and all-monomial reverse rows fill the literal annihilator at
each paid grade 7 through 10, and every rank keeps the terminal debit. -/
theorem order13_reverse_window (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 13)
    {n : ℕ} (lo : 1≤n) (hi : n≤4) :
    back A b n=annih (markedTreeSpace A b (11-n)) ∧
    primitiveBack A b n=annih (markedTreeSpace A b (11-n)) ∧
    finrank K (back A b n)+terminalDebit A b=n+1 := by
  let j := 11-n
  let E := markedTreeSpace A b j
  have r : finrank K E=j+7+terminalDebit A b :=
    order13_paid_high_ranks ha ho (by dsimp [j]; omega) (by dsimp [j]; omega)
  have p : j+n+2≤13 := by dsimp [j]; omega
  have t : terminalDebit A b+finrank K (back A b 0)=1 := terminalDebit_balance A b
  have s : 19≤finrank K E+n+finrank K (back A b 0) := by
    apply le_of_eq
    symm
    rw [r]
    calc
      _ = j+7+n+(terminalDebit A b+finrank K (back A b 0)) := by ac_rfl
      _ = 19 := by rw [t]; dsimp [j]; omega
  have L := order13_last_active ha ho
  have exactPrim : primitiveBack A b n=annih E := primitiveBack_eq_marked_annih_of_rank ha ho L p s
  have lower := back_finrank ha ho n (by omega)
  have ranks : finrank K E+finrank K (annih E)=19 := by
    simpa only [Fintype.card_fin] using finrank_annih E
  have incl : back A b n≤annih E := exactPrim ▸ back_le_primitiveBack n
  have target : finrank K E+(n+finrank K (back A b 0))=19 := by
    rw [r]
    calc
      _ = j+7+n+(terminalDebit A b+finrank K (back A b 0)) := by ac_rfl
      _ = 19 := by rw [t]; dsimp [j]; omega
  have ra : finrank K (annih E)=n+finrank K (back A b 0) :=
    Nat.add_left_cancel (ranks.trans target.symm)
  have exactBack : back A b n=annih E := Submodule.eq_of_le_of_finrank_le incl (by
    rw [ra,Nat.add_comm n]
    exact lower)
  have nr : finrank K (back A b n)+terminalDebit A b=n+1 := by
    rw [exactBack,ra,Nat.add_assoc,Nat.add_comm (finrank K (back A b 0)),t]
  exact ⟨exactBack,exactPrim,nr⟩

theorem order13_marked_reverse_ranks (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 13)
    (first : firstSeed A b=0) (n : ℕ) (hi : n≤4) : finrank K (back A b n)=n := by
  by_cases e : n=0
  · subst n
    exact first_dim_zero first
  · have r := (order13_reverse_window ha ho (n:=n) (by omega) hi).2.2
    rw [show terminalDebit A b=1 by simp [terminalDebit,first]] at r
    omega

end
end RKResearch.Certified.Graded
