module

public import RKCert.ReviewedNative.ERK13NativeLateWidth19
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Conditional assembly of the reviewed order-thirteen stage bound

The ordinary first-seed case and the literal terminal payment are
already available. The only remaining inputs are closures of the two
actual early first-escape charts. This module does not import either
early closure or claim an unconditional Lean stage bound. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse
open scoped Classical Matrix

universe u

/-- A closure on the actual marked width-19 chart. The escape index `a`
means that its paid polynomial has degree `a+1`. The terminal payment is
membership of the original physical last coordinate in `treeSpace A 7`. -/
def EarlyMarkedObstruction13 (K : Type u) [Field K] [CharZero K] (a : ℕ) : Prop :=
  ∀ {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K} {r : ℕ}
    {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K} {G : K[X]},
    (∀ i j, i ≤ j → A i j = 0) → HasOrder 13 A b →
    NativeMarkedEscapeChart A b a G r U w →
    coordinate (K:=K) (Fin.last 18) ∈ treeSpace A 7 → False

/-- With both early charts closed, no strict width-19 method has the
reviewed order thirteen. The seed, paid head, first escape and literal
terminal membership are supplied by the original tableau. -/
theorem width19_impossible_of_early_cuts {K : Type u} [Field K] [CharZero K]
    (earlyFive : EarlyMarkedObstruction13 K 5) (earlySix : EarlyMarkedObstruction13 K 6)
    {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b) : False := by
  by_cases seed : firstSeed A b = 0
  · have terminal := width19_pays_terminal_by_seven ha ho
    obtain ⟨r, U, w, H⟩ := paid_head_of_order ha ho
    obtain ⟨a, G, F⟩ := firstEscape_of_paid_rank ha ho H.paidRanks
    have chart := native_marked_escape_chart ha ho seed H F
    rcases F.width with six | ⟨five, _⟩
    · subst a
      exact earlySix ha ho chart terminal
    · subst a
      exact earlyFive ha ho chart terminal
  · exact ordinary_width19_impossible ha ho seed

/-- The existing unrestricted stage floor leaves just `s=19` below
twenty. This conclusion assumes exactly the two early chart closures. -/
theorem twenty_le_of_order_thirteen_of_early_cuts {K : Type u} [Field K] [CharZero K]
    (earlyFive : EarlyMarkedObstruction13 K 5) (earlySix : EarlyMarkedObstruction13 K 6)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b) : 20 ≤ s := by
  have floor := stage_floor19 ha ho
  by_contra small
  have width : s = 19 := by omega
  subst s
  exact width19_impossible_of_early_cuts earlyFive earlySix ha ho

end RKResearch.Certified.Graded.ERK13NativeFirst
