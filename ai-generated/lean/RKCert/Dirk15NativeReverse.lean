module

public import RKCert.Dirk15DeletedBand
public import RKCert.DirkReverseHermite

@[expose] public section

/-! # Native clock escapes in the true order-fifteen reverse flags
The accounted branches distinguish the full annihilator from its actual
last-coordinate-zero restriction. No shortened method is used. -/
namespace RKCert.Paired
open Module
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

omit [CharZero K] in
theorem terminalZero_eq_reverseHermite (j : ℕ) :
    markedTerminalZero (s:=19) A 15 j=ReverseHermite.zeroMarked A 15 (Fin.last 19) j := by
  unfold markedTerminalZero ReverseHermite.zeroMarked
  congr 1
  ext w
  exact prior_last_iff

omit [CharZero K] in
theorem PhysicalTerminal.column_zero {K : Type*} [Field K] {s : ℕ}
    {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (T : PhysicalTerminal (s:=s) A b) : ∀ i, A i (Fin.last s)=0 := by
  classical
  intro i
  have he := congrFun T.annihilated i
  change mat A (terminalCardinal K s) i=0 at he
  simpa [mat_apply,terminalCardinal,Pi.single_apply] using he

/-- All four terminal-zero escapes needed for the nineteen-coordinate
annihilator band follow from actual Hermite lifts and the saturated ranks. -/
theorem order15_minimal_marked_escape
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b) (j : ℕ) (hl : 4≤j) (hu : j≤7) :
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

/-- The entire deleted band, now without a noninvariance hypothesis.
The branch assumption `dim M4 = 2` is still required. -/
theorem order15_minimal_deleted_band
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b) (j : ℕ) (hl : 7≤j) (hu : j≤11) :
    deletedTreeSpace A j=annih (deletedMarkedZero A (14-j)) ∧
      finrank K (deletedTreeSpace A j)=j+7 :=
  deleted_tree_band h (order15_minimal_marked_escape ha ho h) j hl hu

/-- Any full marked band with actual unit growth at these grades has all
four escapes as well, with no terminal assumption at all. -/
theorem order15_full_marked_escape_of_unit
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (unit : ∀ j : ℕ, 4≤j → j≤6 →
      finrank K (marked A 15 (j+1))≤finrank K (marked A 15 j)+1)
    (j : ℕ) (hl : 4≤j) (hu : j≤7) :
    ¬ (marked A 15 j).map (diag (mirror A))≤marked A 15 j := by
  intro inv
  by_cases hj : j=7
  · subst j
    have he := ReverseHermite.full_incoming ha ho (j:=6) (by decide) inv
    have hb := unit 6 (by decide) (by decide)
    change _+_≤finrank K (marked A 15 7) at he
    change finrank K (marked A 15 7)≤_+1 at hb
    omega
  · have he := ReverseHermite.full_outgoing ha ho (j:=j) (by omega) le_rfl inv
    have hb := unit j hl (by omega)
    omega

end RKCert.Paired
