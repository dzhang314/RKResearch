import RKCert.ReviewedNative.ERK17LocalFiveSaturation

open RKResearch Module
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.LocalLinear RKResearch.Certified.ERK17
open RKCert.Endpoint RKCert.Endpoint.WeightedClock

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ : Fin 26 → K}
variable {r : ℕ} {U : Submodule K (Fin 26 → K)}

example (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (nz : firstSeed A b ≠ 0) (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7 = annih (treeSpace A 8))
    (rank : finrank K (hiddenKernel b τ U) = 5) :
    ∃ W θ : Fin 26 → K, (weightedSites (nodes A) θ).card = 4 ∧
      (∀ i, θ i ≠ 0 ↔ W i ≠ 0) ∧
      (∀ i, θ i ≠ 0 → ∀ v ∈ zeroSpace A 9, v i = 0) := by
  obtain ⟨h, S, Q, e, W, k, θ, G⟩ :=
    width26_tiny_rank_five_physical_producer ha ho nz F full rank
  exact ⟨W, θ, G.feed.sites, G.feed.support, G.feed.clean⟩
end

#print axioms RKResearch.Certified.Graded.PhysicalCensus.exact_supported_triple_live
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.JointBandCensus.physical_live_cover
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.unit_clean_four_feed_of_live_cover
#print axioms RKResearch.Certified.ERK17.width26_rank_five_primitive_nine_cap
#print axioms RKResearch.Certified.ERK17.width26_tiny_rank_five_physical_producer

