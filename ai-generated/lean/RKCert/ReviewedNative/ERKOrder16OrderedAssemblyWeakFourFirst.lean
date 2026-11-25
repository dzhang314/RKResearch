module

public import RKCert.ReviewedNative.ERKOrder16OrderedAssembly
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAccepted

@[expose] public section

/-! # The ordered ERK16 assembly after the first-stop weak-four exclusion

The existing native width-24 dispatch and padding are unchanged. Their only
remaining scalar premise is the literal weak-five packet, not an additional
statement about a physical tableau. -/
namespace RKResearch.Certified.ERK16

open RKResearch Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem weakFourScalarExclusion_of_first_stop : WeakFourScalarExclusion K := by
  intro Q Z a c ports
  exact RKCert.ReviewedNative.WeakFourFirstOnly.Replay.weakFourScalarExclusion_of_accepted_tables
    ports

/-- The reviewed native width-24 split with its actual ordinary ports and
strong branch. The producer still owes exactly `WeakFiveScalarExclusion`. -/
theorem width24_impossible_of_weak_five_scalar_exclusion
    (weakFive : WeakFiveScalarExclusion K)
    (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24 → K)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) : False :=
  width24_impossible_of_weak_scalar_exclusions weakFourScalarExclusion_of_first_stop
    weakFive A b ha ho

/-- Width at least 25, via the reviewed native padding assembly. There is
no separate weak-four, strong, rank, or exterior-clock premise. -/
theorem ordered_erk16_stage_floor25_of_weak_five_scalar_exclusion
    (weakFive : WeakFiveScalarExclusion K)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) : 25 ≤ s :=
  ordered_erk16_stage_floor25_of_weak_scalar_exclusions
    weakFourScalarExclusion_of_first_stop weakFive ha ho

end RKResearch.Certified.ERK16
