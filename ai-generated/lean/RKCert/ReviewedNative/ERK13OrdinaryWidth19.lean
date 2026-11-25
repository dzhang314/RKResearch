module

public import RKCert.ReviewedNative.ERK13OrdinaryRadiusTwo
public import RKCert.ReviewedNative.ERK13OrdinaryRadiusThreeFinish
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exclude the nonzero-first-seed ERK13 width-19 tableau

No assertion is made about the zero-first-seed terminal branch.
-/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Reverse
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}

theorem ordinary_width19_impossible (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0) : False := by
  obtain ⟨G,r,U,w,H⟩ := ordinary_staircase_of_order ha ho seed
  obtain ⟨rank4,rad,_⟩ := ordinary_rank_radius_reduction ha ho seed H
  rcases rad with rfl|rfl
  · exact ordinary_radius_two_four_impossible ha ho seed H rank4
  · exact ordinary_radius_three_impossible ha ho seed H

/-- An order-thirteen explicit method with nonzero first reverse seed
has at least twenty stages over any characteristic-zero field. -/
theorem twenty_le_of_order_thirteen_of_firstSeed_ne_zero
    {s : ℕ} {T : Matrix (Fin s) (Fin s) K} {v : Fin s → K}
    (ha : ∀ i j, i ≤ j → T i j = 0)
    (ho : HasOrder 13 T v) (seed : firstSeed T v ≠ 0) : 20 ≤ s := by
  have h := stage_floor19 ha ho
  by_contra hsmall
  have hs : s = 19 := by omega
  subst s
  exact ordinary_width19_impossible ha ho seed

end
end RKResearch.Certified.Graded.ERK13NativeFirst
