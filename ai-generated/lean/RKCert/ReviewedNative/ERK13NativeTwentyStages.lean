module

public import RKCert.ReviewedNative.ERK13NativePencilScalarCubic
public import RKCert.ReviewedNative.ERK13NativePencilScalarQuartic
public import RKCert.ReviewedNative.ERK13NativeMarkedLobattoDispatch
import Lean.Elab.Tactic.Omega

@[expose] public section
/-! # At least twenty physical stages for explicit reviewed order thirteen

The only mathematical hypotheses are a characteristic-zero field, strict
triangularity on the original stages, and the reviewed rooted-tree order
definition. The ordinary and both marked widths exhaust all literal charts. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst
open RKResearch Reverse Module ERK13NativePencil
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem degree_seven_pencil_impossible {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
    {G : Polynomial K} {r : ℕ} {U : Submodule K (Fin 19→K)} {w : Fin 19→K}
    (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) : False :=
  early_pencil_impossible_of_scalar_ports H ha ho certified_cubic_pencil_cut certified_quartic_pencil_cut

theorem width_nineteen_order_thirteen_impossible {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) : False := by
  by_cases seed : firstSeed A b=0
  · obtain ⟨r,U,w,H⟩ := paid_head_of_order ha ho
    obtain ⟨a,G,F⟩ := firstEscape_of_paid_rank ha ho H.paidRanks
    have C := native_marked_escape_chart ha ho seed H F
    rcases F.width with six | ⟨five,_⟩
    · subst a
      exact degree_seven_pencil_impossible C ha ho
    · subst a
      exact C.degree_six_impossible ha ho
  · exact ordinary_width19_impossible ha ho seed

theorem twenty_le_of_order_thirteen {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) : 20≤s := by
  have lo := stage_floor19 ha ho
  by_contra small
  have e : s=19 := by omega
  subst s
  exact width_nineteen_order_thirteen_impossible ha ho

end
end RKResearch.Certified.Graded.ERK13NativeFirst
