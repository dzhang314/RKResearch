module

public import RKCert.ReviewedNative.NativeRowOrderDefects
public import RKCert.ReviewedNative.ERK13NativeLateWidth19
public import RKCert.ReviewedNative.ERK13NativeMarkedEarlyMode

@[expose] public section

/-! # The actual terminal output row forced at width 19 and order 13

The endpoint row and its literal 18-stage prefix satisfy the original
order-six conditions. Its next order holds precisely when the early
grade-seven defect space has no measured extra mode. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst
open RKResearch Polynomial Reverse Module
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}

theorem width19_last_node_clean_six
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    nodes A (Fin.last 18)=1 ∧ ∀x∈zeroSpace A 6,x (Fin.last 18)=0 := by
  have seed : firstSeed A b=0 := by
    by_contra nz
    exact ordinary_width19_impossible ha ho nz
  obtain ⟨r,U,w,H⟩ := paid_head_of_order ha ho
  obtain ⟨a,G,F⟩ := firstEscape_of_paid_rank ha ho H.paidRanks
  have C := native_marked_escape_chart ha ho seed H F
  have eq : zeroSpace A 6=escapeHeadBand A U w (r+1) := H.head.flags 1 (by decide)
  refine ⟨H.paidRanks.lastActive.node_eq_one ha seed,?_⟩
  intro x hx
  exact C.early_head_last_zero ho (width19_pays_terminal_by_seven ha ho) (eq ▸ hx)

theorem width19_last_row_hasOrder_six
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    HasOrder 6 A (A (Fin.last 18)) :=
  let h := width19_last_node_clean_six ha ho
  row_hasOrder_of_clean_clock_one h.1 h.2

theorem width19_last_prefix_hasOrder_six
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    HasOrder 6 (prefixMatrix A (by decide : 18≤19))
      (fun j:Fin 18=>A (Fin.last 18) (Fin.castLE (by decide : 18≤19) j)) := by
  obtain ⟨one,clean⟩ := width19_last_node_clean_six ha ho
  have nz : nodes A (Fin.last 18)≠0 := by rw [one]; exact one_ne_zero
  have p := exact_receiver_prefix_order ha (Fin.last 18) 6 nz clean
  simp only [one, inv_one, one_smul, one_mul] at p
  exact p

theorem NativeMarkedEscapeChart.early_last_row_seven_iff_head
    {r a : ℕ} {U : Submodule K (Fin 19→K)} {w : Fin 19→K} {G : K[X]}
    (C : NativeMarkedEscapeChart A b a G r U w) (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7) :
    HasOrder 7 A (A (Fin.last 18)) ↔ zeroSpace A 7=escapeHeadBand A U w (r+2) := by
  have atOne := C.head.paidRanks.lastActive.node_eq_one ha C.seed
  constructor
  · intro h
    rcases C.early_F7_mode ha ho early with pure | ⟨J,M⟩
    · exact pure
    · have bad := zeroSpace_at_row_hasOrder h _ M.paid
      rw [evalNodes_apply,atOne,M.lastOne] at bad
      exact (one_ne_zero bad).elim
  · intro shape
    apply row_hasOrder_of_clean_clock_one atOne
    intro x hx
    exact C.early_head_last_zero ho early (shape ▸ hx)

end
end RKResearch.Certified.Graded.ERK13NativeFirst
