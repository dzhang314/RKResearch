module

public import RKCert.ReviewedNative.ERK13NativeWidth19EndpointOrder
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # A width-19 endpoint of order seven forces radius two

At every other actual head radius the endpoint output cannot have order
seven. Since it has order six unconditionally, a genuine rooted tree of
order exactly seven witnesses the failure. This is not only a failed
quadrature moment; the witness is in the original order language. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst
open RKResearch Polynomial Reverse Module
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {r : ℕ} {U : Submodule K (Fin 19→K)} {w : Fin 19→K}

theorem pure_endpoint_radius_two
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (H : NativePaidHead A b r U w)
    (rowSeven : HasOrder 7 A (A (Fin.last 18))) : r=2 := by
  have seed : firstSeed A b=0 := by
    by_contra nz
    exact ordinary_width19_impossible ha ho nz
  obtain ⟨a,G,F⟩ := firstEscape_of_paid_rank ha ho H.paidRanks
  have C := native_marked_escape_chart ha ho seed H F
  exact C.radius_two_of_seven_head ha ho
    ((C.early_last_row_seven_iff_head ha ho (width19_pays_terminal_by_seven ha ho)).mp rowSeven)

theorem actual_seven_witness_of_radius_ne_two
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativePaidHead A b r U w) (other : r≠2) :
    ∃ t : FiniteRootedTree, (t.order:ℕ)=7 ∧
      (t.factorial:K)*(A (Fin.last 18) ⬝ᵥ Φ t A)≠1 := by
  classical
  by_contra no
  apply other (pure_endpoint_radius_two ha ho H ?_)
  intro t ht
  by_cases lo : (t.order:ℕ)≤6
  · exact width19_last_row_hasOrder_six ha ho t lo
  · by_contra fail
    exact no ⟨t,by omega,fail⟩

end
end RKResearch.Certified.Graded.ERK13NativeFirst
