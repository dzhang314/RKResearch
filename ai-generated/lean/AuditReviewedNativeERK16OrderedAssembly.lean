import RKCert.ReviewedNative.ERKOrder16OrderedAssembly

open RKResearch Polynomial RKResearch.Certified.ERK16

-- Audit the actual width-24 exclusion, with no seed or rank assumption.
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (weakFour : WeakFourScalarExclusion K) (weakFive : WeakFiveScalarExclusion K)
    {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) : False :=
  width24_impossible_of_weak_scalar_exclusions weakFour weakFive A b ha ho

-- Independently expand the two scalar premises at arbitrary width.
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (weakFour : ∀ {Q Z : K[X]} {a c : K},
      WeakFourChronologicalPorts Q Z a c → False)
    (weakFive : ∀ {q Z : K[X]} {c : Fin 5 → K},
      RKCert.ReviewedNative.WeakFive16.Moments q Z c → False)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) : 25 ≤ s :=
  ordered_erk16_stage_floor25_of_weak_scalar_exclusions weakFour weakFive ha ho

#print axioms RKResearch.Certified.ERK16.width24_native_head_dispatch
#print axioms RKResearch.Certified.ERK16.width24_strong_seventh_rank_ne_eight
#print axioms RKResearch.Certified.ERK16.width24_impossible_of_weak_scalar_exclusions
#print axioms RKResearch.Certified.ERK16.ordered_erk16_stage_floor25_of_weak_scalar_exclusions
