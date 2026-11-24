import RKCert.ReviewedNative.ERK19OrderedFloor30

open RKResearch Polynomial RKCert.ReviewedNative.ERK19ZeroScalar

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K[X]} {z : Fin 4 → K} {e : ℕ} (h : OpposedQuinticWindows P z e) : False :=
  opposed_quintic_windows_impossible h

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 19 A b) : 30 ≤ s :=
  RKResearch.Certified.ERK19.ordered_erk19_stage_floor30 ha ho

#print axioms RKCert.ReviewedNative.ERK19ZeroScalar.opposed_quintic_clock_location
#print axioms RKCert.ReviewedNative.ERK19ZeroScalar.OpposedQuinticWindows.local_impossible
#print axioms RKCert.ReviewedNative.ERK19ZeroScalar.opposed_quintic_windows_impossible
#print axioms RKResearch.Certified.ERK19.ordered_erk19_stage_floor30
