module

public import RKCert.ReviewedNative.ERKOrder16OrderedAssemblyWeakFourFirst
public import RKCert.ReviewedNative.ERKOrder16WeakFivePartialScalarExclusion
public import RKCert.ReviewedNative.ERKOrder16WeakFiveSoleInnerChronology
public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralEndpoint

@[expose] public section

/-! # Reviewed ordered ERK16 stage floor

The final facade consumes the two closed literal weak-five callbacks at the
already reviewed assembly. No table, chronology, or extra condition on the
Runge–Kutta tableau is a premise. -/
namespace RKResearch.Certified.ERK16

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem weakFive_scalar_closed_literals : WeakFiveScalarExclusion K :=
  weak_five_scalar_exclusion_of_sole_inner_three_interior
    (fun M S => RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells.no_actual_sole_inner M S)
    (fun M T => RKCert.ReviewedNative.ThreeInteriorPencil.no_actual_threeInterior_of_literal_table M T)

/-- No strict lower-triangular 24-stage tableau has reviewed order 16. -/
theorem ordered_erk16_width24_impossible
    {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
    (strict : ∀ i j, i ≤ j → A i j = 0) (order : RKResearch.HasOrder 16 A b) : False :=
  width24_impossible_of_weak_five_scalar_exclusion
    (weakFive_scalar_closed_literals (K := K)) A b strict order

/-- The width floor over any ordered field, including all smaller widths. -/
theorem ordered_erk16_stage_floor25
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (strict : ∀ i j, i ≤ j → A i j = 0) (order : RKResearch.HasOrder 16 A b) : 25 ≤ s :=
  ordered_erk16_stage_floor25_of_weak_five_scalar_exclusion
    (weakFive_scalar_closed_literals (K := K)) strict order

end RKResearch.Certified.ERK16
