import RKCert.ReviewedNative.ERKOrder16NativeHeadDispatch

open RKResearch Module Polynomial RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin RKResearch.Certified.ERK16
open RKCert.ReviewedNative.StrongCentered16

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) :
    firstSeed A b = 0 ∧
      (finrank K (zeroSpace A 7) = 7 ∨ finrank K (zeroSpace A 7) = 8) :=
  width24_seed_zero_and_seventh_rank_cases ha ho

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) :
    Width24PaidFrame A b ∧
      ((finrank K (zeroSpace A 7) = 7 ∧
        ∃ (U : Submodule K (Fin 24 → K)) (w : Fin 24 → K) (Q P : K[X]),
          Width24OrdinaryWeakHead A b U w Q P ∧
            ((weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4 ∨
              (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 5)) ∨
        (finrank K (zeroSpace A 7) = 8 ∧
          ∃ (w g : Fin 24 → K) (Q P : K[X]) (ι : Fin 3 → Fin 24),
            StrongThreeActualMask A b w g Q P ∧
              StrongThreePhysicalPorts A b Q P ι ∧ ι 0 = 0 ∧
                Moments (Q.comp (1-X)) (nodes A (ι 1)) (nodes A (ι 2)))) :=
  width24_native_head_dispatch ha ho

#print axioms RKResearch.Certified.ERK16.width24_seventh_rank_cases_of_eighth
#print axioms RKResearch.Certified.ERK16.width24_first_seed_eq_zero
#print axioms RKResearch.Certified.ERK16.width24_seventh_rank_cases_of_frame
#print axioms RKResearch.Certified.ERK16.width24_seed_zero_and_seventh_rank_cases
#print axioms RKResearch.Certified.ERK16.width24_native_head_dispatch
