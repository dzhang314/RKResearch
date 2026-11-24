import RKCert.ReviewedNative.ERKOrder16WeakContrastCases

open RKResearch Module Polynomial RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin RKResearch.Certified.ERK16

example {K : Type*} [Field K] [CharZero K] {s p r : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {Q P : K[X]}
    (ho : HasOrder p A b) (qn : Q ≠ 0)
    (qpay : 2 * Q.natDegree + 2 * r + 2 ≤ p)
    (ppay : Q.natDegree + P.natDegree + 2 * r + 3 ≤ p) :
    r < (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card :=
  reverse_contrast_sites_gt_of_paid_moments ho qn qpay ppay

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7) :
    ∃ (U : Submodule K (Fin 24 → K)) (w : Fin 24 → K) (Q P : K[X]),
      Width24OrdinaryWeakHead A b U w Q P ∧
        ((weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4 ∨
          (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 5) :=
  width24_ordinary_weak_contrast_cases ha ho seven

#print axioms RKResearch.Certified.Graded.Reverse.Thin.reverse_contrast_sites_gt_of_paid_moments
#print axioms RKResearch.Certified.ERK16.width24_ordinary_weak_contrast_four_or_five
#print axioms RKResearch.Certified.ERK16.width24_ordinary_weak_contrast_cases
