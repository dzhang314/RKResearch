import RKCert.ReviewedNative.LocalLinearCleanFourMassHull

open RKResearch Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour
open RKCert.Endpoint.WeightedClock RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b τ h W k θ : Fin s → K}
variable {U : Submodule K (Fin s → K)} {S Q : K[X]}

example (ho : HasOrder 17 A b)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    (B : UnitFourCompensated A b τ W U S Q)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    {x : K} (hx : x ∈ weightedSites (nodes A) θ) (R : K[X]) (rd : R.natDegree ≤ 2) :
    0 < blockMass (nodes A) θ b x ∧
      (∑ z ∈ weightedSites (nodes A) θ, blockMass (nodes A) θ W z *
        (R.eval z * coefficient A θ (ordinaryProfile Q) z x)) =
        blockMass (nodes A) θ b x * integral x 1 (R*ordinaryProfile Q) := by
  refine ⟨B.block_mass_pos ho (by decide) G hx
    (indicator_paid ho (by decide) G inside stable hx), ?_⟩
  exact B.transpose_block_moment ho (by decide) G inside stable hx R rd

end

#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.cardinalTest_evaluation
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.indicator_paid
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.coefficient_eq_zero_before
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.forward_block_moment
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.forward_mask_zero
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.firstRow_origin
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.UnitFourCompensated.moment_sum
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.UnitFourCompensated.reverse_residual
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.UnitFourCompensated.transpose_block_moment
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.UnitFourCompensated.reverse_mask_zero
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.UnitFourCompensated.block_mass_pos
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.UnitFourCompensated.hull_moment
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour.nonzero_clock_interior_of_origin_hull
