module

public import RKCert.Dirk15WeightedLocalCut
public import RKCert.DirkWeightedFourComplete

@[expose] public section

/-! # The actual minimal order-fifteen reverse cubic is nonlocal -/
namespace RKCert.Paired

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

theorem order15_cubic_budget_nonlocal (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15CubicBudget A b) :
    ¬ (markedTerminalZero (s:=19) A 15 3).map
      (diag (mirror A))≤markedTerminalZero (s:=19) A 15 3 := by
  intro inv
  obtain ⟨D⟩ := order15_local_projects_to_weighted_cut ha ho h inv
  exact LocalProjection.WeightedFour.impossible D

theorem order15_minimal_reverse_nonlocal (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b) :
    ¬ (markedTerminalZero (s:=19) A 15 3).map
      (diag (mirror A))≤markedTerminalZero (s:=19) A 15 3 :=
  order15_cubic_budget_nonlocal ha ho h.cubic_budget

theorem order15_nonC2_reverse_nonlocal (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15NonC2Chart A b) :
    ¬ (marked A 15 3).map (diag (mirror A))≤marked A 15 3 := by
  rw [h.marked_terminal_zero ha ho 3 (by decide) (by decide)]
  exact order15_cubic_budget_nonlocal ha ho (h.cubic_budget ha ho)

end RKCert.Paired
