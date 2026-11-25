import RKCert.ReviewedNative.ERK17LocalFourClosure

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.LocalLinear RKResearch.Certified.ERK17
open RKResearch.Certified.Graded.PhysicalCensus RKCert.Endpoint RKCert.Endpoint.WeightedClock

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ : Fin 26 → K}
variable {r : ℕ} {U : Submodule K (Fin 26 → K)}

example (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (nz : firstSeed A b ≠ 0) (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7 = annih (treeSpace A 8))
    (rank : finrank K (hiddenKernel b τ U) = 4) :
    ∃ ξ W θ : Fin 26 → K, (activeLabels (jointClock (reflectedClock A) ξ) τ).card = 16 ∧
      (weightedSites (reflectedClock A) W).card = 4 ∧
      (∀ i, θ i ≠ 0 ↔ W i ≠ 0) ∧
      (∀ i, θ i ≠ 0 → ∀ v ∈ zeroSpace A 9, v i = 0) := by
  obtain ⟨h,ξ,S,Q,e,W,k,θ,G⟩ :=
    width26_tiny_rank_four_physical_producer ha ho nz F full rank
  exact ⟨ξ,W,θ,G.rankHead,G.rankContrast,G.feed.support,G.feed.clean⟩

example (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (nz : firstSeed A b ≠ 0) (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7 = annih (treeSpace A 8))
    (rank : finrank K (hiddenKernel b τ U) = 4) : False :=
  width26_tiny_rank_four_impossible ha ho nz F full rank

end

#print axioms RKResearch.Certified.Graded.PhysicalCensus.labelOrbit_rank
#print axioms RKResearch.Certified.Graded.PhysicalCensus.activeLabels_card_project_lt
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.weighted_tests_one_more_of_top
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.weighted_tests_one_more_of_linear_advance
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.clock_masses_zero_of_significant_sites
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.RefinedJointBandCensus.physical_live_cover
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.JointBandCensus.cancelled_rank_with_silent_extra
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.actual_axis_split_of_silent_local_mode
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.affine_weighted_axis_advance
#print axioms RKResearch.Certified.ERK17.width26_local_four_actual_advance
#print axioms RKResearch.Certified.ERK17.width26_local_four_refined_head_count
#print axioms RKResearch.Certified.ERK17.width26_tiny_rank_four_physical_producer
#print axioms RKResearch.Certified.ERK17.width26_tiny_rank_four_impossible
