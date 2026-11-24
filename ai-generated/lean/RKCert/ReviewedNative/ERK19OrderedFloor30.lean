module

public import RKCert.ReviewedNative.ERK19OpposedAssembly
public import RKCert.ReviewedNative.ERK19ZeroScalarClose

@[expose] public section

namespace RKResearch.Certified.ERK19

open RKResearch Polynomial RKCert.ReviewedNative.ERK19ZeroScalar
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Order nineteen requires thirty stages over every ordered field. -/
theorem ordered_erk19_stage_floor30 {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 19 A b) : 30 ≤ s :=
  ordered_erk19_stage_floor30_of_zero_scalar
    (fun _ _ _ H => opposed_quintic_windows_impossible H) ha ho

end RKResearch.Certified.ERK19
