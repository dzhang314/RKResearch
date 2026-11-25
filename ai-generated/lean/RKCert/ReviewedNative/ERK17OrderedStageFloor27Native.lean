module

public import RKCert.ReviewedNative.ERK17OrderedActualAssembly
public import RKCert.ReviewedNative.ERK17RadauFirstResidueNative
public import RKCert.ReviewedNative.OrderedOriginSmallestClock

@[expose] public section

/-! # Ordered explicit Runge–Kutta methods of order 17 need at least 27 stages -/
namespace RKResearch.Certified.ERK17

open RKResearch RKCert.ReviewedNative.OriginSignedSquares

/-- The ordered stage lower bound on the literal reviewed order predicate. -/
theorem ordered_erk17_stage_floor27_native
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : 27 ≤ s :=
  ordered_erk17_stage_floor27_of_actual_origin_gates
    native_radau_first_gate_of_residue noSmallestClock_of_pole_sign_cuts ha ho

end RKResearch.Certified.ERK17
