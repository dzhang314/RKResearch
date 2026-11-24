import RKCert.ReviewedNative.ERK19ZeroGlobalLocation

open Polynomial RKCert.ReviewedNative.ERK19ZeroScalar

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K[X]} {z : Fin 4 → K} {e : ℕ} (H : OpposedQuinticWindows P z e) :
    (exteriorClockIndices z).card ≤ e :=
  opposed_quintic_exterior_budget H

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (H : OpposedQuinticWindows P z e) :
    0 < z 0 ∧ z 3 < 1 ∧ z 1 ∈ Set.Ioo (0 : K) 1 ∧ z 2 ∈ Set.Ioo (0 : K) 1 :=
  opposed_quintic_clock_location H

#print axioms RKCert.ReviewedNative.ERK19ZeroScalar.opposed_quintic_exterior_budget
#print axioms RKCert.ReviewedNative.ERK19ZeroScalar.opposed_quintic_clock_location
