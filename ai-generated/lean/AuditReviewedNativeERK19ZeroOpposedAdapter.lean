import RKCert.ReviewedNative.ERK19ZeroOpposedAdapter

open RKResearch RKResearch.Certified.Graded.Reverse
open RKCert.ReviewedNative.ERK19ZeroScalar
open Polynomial

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29 → K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 19 A b)
    (zero : firstSeed A b=0) :
    ∃ (P : K[X]) (z : Fin 4 → K) (e : ℕ), OpposedQuinticWindows P z e :=
  RKResearch.Certified.ERK19.width29_zero_opposed_windows ha ho zero

#print axioms RKResearch.Certified.ERK19.width29_opposed_physical_rows
#print axioms RKResearch.Certified.ERK19.width29_zero_geometry_to_opposed_windows
#print axioms RKResearch.Certified.ERK19.width29_zero_opposed_windows
