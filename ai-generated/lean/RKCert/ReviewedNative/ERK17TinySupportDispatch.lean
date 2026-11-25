module

public import RKCert.ReviewedNative.ERK17LocalFourClosure
public import RKCert.ReviewedNative.ERK17LocalFiveClosure

@[expose] public section

/-! # Dispatch the two actual tiny first-seed numerical supports

The first seed is nonzero. The local frame is produced from the actual
support count, and the paid kernel rank sandwich earns every endpoint
premise. No zero-seed or broader-support proof is imported. -/
namespace RKResearch.Certified.ERK17

open RKResearch Module
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.LocalLinear RKCert.Endpoint.WeightedClock
open scoped Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ordered_width26_tiny_nonzero_first_impossible
    {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (nz : firstSeed A b ≠ 0)
    (tiny : (weightedSites (reflectedClock A) (firstSeed A b)).card ≤ 2) : False := by
  obtain ⟨r,U,τ,F,full⟩ := width26_tiny_first_seed_local_frame ha ho nz tiny
  have flags := width26_tiny_hidden_rank ha ho nz F full
  have lower : 4 ≤ finrank K (hiddenKernel b τ U) := flags.2.2.2.2.1
  have upper : finrank K (hiddenKernel b τ U) ≤ 5 := flags.2.2.2.2.2
  have rank : finrank K (hiddenKernel b τ U) = 4 ∨ finrank K (hiddenKernel b τ U) = 5 := by
    omega
  rcases rank with four | five
  · exact width26_tiny_rank_four_impossible ha ho nz F full four
  · exact width26_tiny_rank_five_impossible ha ho nz F full five

end
end RKResearch.Certified.ERK17
