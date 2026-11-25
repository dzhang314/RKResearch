module

import RKCert.ReviewedNative.ERKOrder16OrderedAssemblyWeakFourFirst

open RKResearch Polynomial RKResearch.Certified.ERK16

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ∀ {Q Z : K[X]} {a c : K}, WeakFourChronologicalPorts Q Z a c → False :=
  weakFourScalarExclusion_of_first_stop

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (weakFive : ∀ {q Z : K[X]} {c : Fin 5 → K},
      RKCert.ReviewedNative.WeakFive16.Moments q Z c → False)
    {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) : False :=
  width24_impossible_of_weak_five_scalar_exclusion weakFive A b ha ho

-- Arbitrary width, with the one remaining scalar premise expanded.
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (weakFive : ∀ {q Z : K[X]} {c : Fin 5 → K},
      RKCert.ReviewedNative.WeakFive16.Moments q Z c → False)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) : 25 ≤ s :=
  ordered_erk16_stage_floor25_of_weak_five_scalar_exclusion weakFive ha ho

#print axioms RKResearch.Certified.ERK16.weakFourScalarExclusion_of_first_stop
#print axioms RKResearch.Certified.ERK16.width24_impossible_of_weak_five_scalar_exclusion
#print axioms RKResearch.Certified.ERK16.ordered_erk16_stage_floor25_of_weak_five_scalar_exclusion
