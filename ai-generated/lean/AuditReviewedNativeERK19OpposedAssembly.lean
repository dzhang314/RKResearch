import RKCert.ReviewedNative.ERK19OpposedAssembly

open RKResearch Polynomial
open RKCert.ReviewedNative.ERK19ZeroScalar

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (cut : ∀ (P : K[X]) (z : Fin 4 → K) (e : ℕ),
      OpposedQuinticWindows P z e → False)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 19 A b) : 30 ≤ s :=
  RKResearch.Certified.ERK19.ordered_erk19_stage_floor30_of_zero_scalar cut ha ho

#print axioms RKResearch.Certified.ERK19.width29_zero_first_seed_impossible_of_scalar
#print axioms RKResearch.Certified.ERK19.ordered_erk19_stage_floor30_of_zero_scalar
