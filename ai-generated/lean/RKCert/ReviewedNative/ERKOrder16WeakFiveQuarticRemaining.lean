module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveExteriorClassifier
public import RKCert.ReviewedNative.ERKOrder16WeakFiveLowDegree

@[expose] public section

namespace RKResearch.Certified.ERK16

open Polynomial Module RKCert.Endpoint.WeightedClock
open RKCert.ReviewedNative.WeakFive16
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse.Thin

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The same original moment packet has degree four and at most one
exterior marked clock. -/
theorem width24_weak_five_quartic_remaining
    {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K} {Q P : K[X]}
    {U : Submodule K (Fin 24 → K)}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7)
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (five : 5 ≤ (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card) :
    ∃ (q Z : K[X]) (c : Fin 5 → K), Moments q Z c ∧
      q.natDegree = 4 ∧ (exteriorMarkedClocks c).card ≤ 1 := by
  obtain ⟨q, Z, c, M⟩ := width24_weak_five_moments_of_ordinary_head ha ho seven L five
  exact ⟨q, Z, c, M, M.natDegree_eq_four_of_full_packet, M.exterior_count_le_one⟩

end RKResearch.Certified.ERK16
