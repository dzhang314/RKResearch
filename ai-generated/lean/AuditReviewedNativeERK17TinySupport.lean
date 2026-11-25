import RKCert.ReviewedNative.ERK17TinySupportDispatch

open RKResearch RKResearch.Certified.ERK17
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKCert.Endpoint.WeightedClock

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (nz : firstSeed A b ≠ 0)
    (tiny : (weightedSites (reflectedClock A) (firstSeed A b)).card ≤ 2) : False :=
  ordered_width26_tiny_nonzero_first_impossible ha ho nz tiny

#print axioms RKResearch.Certified.ERK17.ordered_width26_tiny_nonzero_first_impossible
