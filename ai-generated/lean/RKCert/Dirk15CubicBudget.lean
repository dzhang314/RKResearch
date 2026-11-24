module

public import RKCert.Dirk15Structural
public import RKCert.Dirk15CubicOrbit

@[expose] public section

/-! # The common original rank budget behind the two minimal cubic flags -/
namespace RKCert.Paired
open Module RKCert.OneEscape

variable {K : Type*} [Field K] {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

/-- This common budget does not require an initial zero row or specify
whether the true terminal cardinal is in E7. -/
structure Order15CubicBudget (A : Fin 20 → Fin 20 → K) (b : Vec K 20) : Prop where
  terminal : PhysicalTerminal (s:=19) A b
  paid_terminal_zero : ∀ j : ℕ, 2 ≤ j → j≤7 →
    markedTerminalZero (s:=19) A 15 j=dirkBack A b (j-2)
  rankTerminalZero : ∀ j : ℕ, 2 ≤ j → j≤7 →
    finrank K (markedTerminalZero (s:=19) A 15 j)=j-2

theorem Order15MinimalMarkedChart.cubic_budget (h : Order15MinimalMarkedChart A b) :
    Order15CubicBudget A b := ⟨h.terminal,h.paid_terminal_zero,h.rankTerminalZero⟩

theorem Order15NonC2Chart.marked_terminal_zero (h : Order15NonC2Chart A b)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (j : ℕ) (hj : 2≤j) (hu : j≤7) :
    marked A 15 j=markedTerminalZero (s:=19) A 15 j := by
  calc
    marked A 15 j = dirkBack A b (j-2) := h.all_paid j hj hu
    _ = markedTerminalZero (s:=19) A 15 j := by
      apply le_antisymm
      · exact back_sub_markedTerminalZero ha ho h.terminal hj (by omega)
      · rw [←h.all_paid j hj hu]
        exact inf_le_left

theorem Order15NonC2Chart.cubic_budget (h : Order15NonC2Chart A b)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) :
    Order15CubicBudget A b := by
  refine ⟨h.terminal,fun j hl hu => ?_,fun j hl hu => ?_⟩
  · rw [←h.marked_terminal_zero ha ho j hl hu,h.all_paid j hl hu]
  · rw [←h.marked_terminal_zero ha ho j hl hu,h.marked_rank_exact j hl hu]

variable [CharZero K]

theorem order15_cubic_budget_escape (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15CubicBudget A b) (j : ℕ) (hl : 4≤j) (hu : j≤7) :
    ¬ (markedTerminalZero (s:=19) A 15 j).map (diag (mirror A))≤
      markedTerminalZero (s:=19) A 15 j := by
  have rank (k : ℕ) (hk : 4≤k) (hK : k≤7) :
      finrank K (ReverseHermite.zeroMarked A 15 (Fin.last 19) k)=k-2 := by
    rw [←terminalZero_eq_reverseHermite]
    exact h.rankTerminalZero k (by omega) hK
  rw [terminalZero_eq_reverseHermite]
  by_cases he : j=7
  · subst j
    exact ReverseHermite.terminal_escape_in ha ho (j:=6) (by decide) (by decide)
      (Fin.last 19) h.terminal.node_one h.terminal.column_zero (by
        rw [rank 6 (by decide) (by decide),rank 7 (by decide) (by decide)])
  · exact ReverseHermite.terminal_escape_out ha ho (by omega) hl
      (Fin.last 19) h.terminal.node_one h.terminal.column_zero (by
        rw [rank j hl hu,rank (j+1) (by omega) (by omega)]
        omega)

end RKCert.Paired
