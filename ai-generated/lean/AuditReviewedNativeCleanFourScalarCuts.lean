import RKCert.ReviewedNative.ERK17LocalFiveClosure

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.LocalLinear RKResearch.Certified.ERK17
open RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour
open RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.ReviewedNative.FiniteOrderedSigns

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ h W k θ : Fin 26 → K}
variable {r : ℕ} {U : Submodule K (Fin 26 → K)} {S Q : K[X]}

example (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (B : UnitFourCompensated A b τ W U S Q)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    (origin : (0 : K) ∈ weightedSites (nodes A) θ) :
    ∃ a d c : K, OpposedThreePivotMoments (ordinaryProfile Q) X 1 a d c := by
  let E : FeedChronology (nodes A) θ 4 := feedChronology G.sites
  exact ⟨E.clock 1, E.clock 2, E.clock 3,
    E.opposed_moments_of_origin (E.clock_zero_of_origin (m:=3) ha G inside origin)
      B ha ho (by decide) G inside stable⟩

example (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (nz : firstSeed A b ≠ 0) (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7 = annih (treeSpace A 8))
    (rank : finrank K (hiddenKernel b τ U) = 5) : False :=
  width26_tiny_rank_five_impossible ha ho nz F full rank

end

#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.feedChronology
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.FeedChronology.clock_zero_of_origin
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.FeedChronology.forward_primitive_zero
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.FeedChronology.reverse_interval_zero
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.FeedChronology.opposed_moments_of_origin
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.clean_four_no_origin_impossible
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.UnitFourCompensated.clean_four_origin_impossible
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.UnitFourCompensated.clean_four_impossible
#print axioms RKResearch.Certified.ERK17.width26_tiny_rank_five_impossible
