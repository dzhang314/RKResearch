module

public import RKCert.ReviewedNative.ERK17LocalFourSaturation
public import RKCert.ReviewedNative.LocalLinearCleanFourScalarCuts

@[expose] public section

/-! # Width-26 order-17 local rank-four exclusion -/
namespace RKResearch.Certified.ERK17

open RKResearch Module
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour
open scoped Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ : Fin 26 → K}
variable {r : ℕ} {U : Submodule K (Fin 26 → K)}

/-- The real refined cover pays exactly the same scalar cut as the
checked rank-five branch, without assuming the ordinary τ count. -/
theorem width26_tiny_rank_four_impossible
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (nz : firstSeed A b ≠ 0) (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7 = annih (treeSpace A 8))
    (rank : finrank K (hiddenKernel b τ U) = 4) : False := by
  have r2 := (width26_tiny_rank_four_refinement ha ho nz F full rank).1
  subst r
  obtain ⟨h,ξ,S,Q,e,W,k,θ,G⟩ :=
    width26_tiny_rank_four_physical_producer ha ho nz F full rank
  have B : UnitFourCompensated A b τ W U S Q :=
    UnitFourCompensated.of_local_trace F G.trace G.compensation
  have inside : hiddenKernel b τ U ≤ zeroSpace A 8 :=
    G.coreInside.trans (zeroSpace_mono A (by decide : 5 ≤ 8))
  exact B.clean_four_impossible ha ho (by decide) G.feed inside
    (hiddenKernel_forward_clock_of_band F)

end
end RKResearch.Certified.ERK17
