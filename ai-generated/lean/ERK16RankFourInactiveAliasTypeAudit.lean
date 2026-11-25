module

import RKCert.ReviewedNative.ERKOrder16WeakFourRankFour
import RKCert.ReviewedNative.ERKOrder16WeakFourInactiveAlias

/-! Standalone type/axiom audit for the two staged public cuts, not a
project dependency. Reviewed order source: ec3d162eda1040c3e22f7f80afd0ffdeeb6f07d0,
OrderConditions.lean SHA-256 c979b6d7d376a78029591091e331a7bfe3484e26cda483f2c0a38367124a01a2.
The literal hypothesis RKResearch.HasOrder concerns the reviewed
FiniteRootedTree, Φ, and factorial; no compatibility theorem is involved.
Using @ directly against the complete Pi type avoids auto-inserting
extra implicit premises. The ordered-field instances are explicit in
both expected types; neither check takes an extra DecidableEq or
topological structure. -/

set_option autoImplicit false

open RKResearch.Certified.ERK16
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint.WeightedClock

universe u

-- Four numerical contrast sites, without any input count of physical rows.
-- The rank four is the compensated carrier rank, not the rank of U.
example :
    ∀ {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
      {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K}
      {U : Submodule K (Fin 24 → K)} {Q P : Polynomial K},
      Width24OrdinaryWeakHead A b U w Q P →
      (∀ i j, i ≤ j → A i j = 0) →
      RKResearch.HasOrder 16 A b →
      Module.finrank K (zeroSpace A 7) = 7 →
      Module.finrank K (width24WeakFiveCarrier A b) = 4 →
      (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4 →
      False :=
  @Width24OrdinaryWeakHead.weak_four_carrier_four_impossible

-- The four-site and four-row premises are separate. The original origin
-- is inactive; another active row shares its numerical reflected clock.
-- There is no extra F7 rank, original b 0, or original seed-zero premise.
example :
    ∀ {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
      {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K}
      {U : Submodule K (Fin 24 → K)} {Q P : Polynomial K},
      Width24OrdinaryWeakHead A b U w Q P →
      (∀ i j, i ≤ j → A i j = 0) →
      RKResearch.HasOrder 16 A b →
      Module.finrank K (width24WeakFiveCarrier A b) = 3 →
      (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4 →
      (weakFiveRows A b Q P).card = 4 →
      (0 : Fin 24) ∉ weakFiveRows A b Q P →
      (∃ j ∈ weakFiveRows A b Q P, reflectedClock A j = 1) →
      False :=
  @Width24OrdinaryWeakHead.weak_four_inactive_origin_shared_clock_impossible

#print axioms RKResearch.Certified.ERK16.Width24OrdinaryWeakHead.weak_four_carrier_four_impossible
#print axioms RKResearch.Certified.ERK16.Width24OrdinaryWeakHead.weak_four_inactive_origin_shared_clock_impossible
