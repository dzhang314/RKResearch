module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveQuadraticCutoff
public import RKCert.ReviewedNative.ERKOrder16WeakFiveExteriorCharge
public import RKCert.ReviewedNative.ERKOrder16WeakFiveCubicCutoff
public import RKCert.ReviewedNative.ERKOrder16WeakFiveAdapter
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.WeakFive16

open Polynomial
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The finite charge eliminates degrees zero and one, and the
quadratic endpoint uses the same original packet. -/
theorem Moments.natDegree_not_le_two {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) : ¬ q.natDegree ≤ 2 := by
  intro small
  have lower := M.exterior_count_add_two_le_degree
  exact M.natDegree_ne_two (by omega)

/-- Only the genuine quartic remains on the complete weak-five packet. -/
theorem Moments.natDegree_eq_four_of_full_packet {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) : q.natDegree = 4 := by
  have small := M.natDegree_not_le_two
  have cubic := M.natDegree_ne_three
  have upper := M.qDegree
  omega

end RKCert.ReviewedNative.WeakFive16

namespace RKResearch.Certified.ERK16

open Polynomial Module RKCert.Endpoint.WeightedClock
open RKCert.ReviewedNative.WeakFive16
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse.Thin

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The actual five-site head produces a quartic on its original labels,
not a fresh scalar chart with an assumed degree. -/
theorem width24_weak_five_has_quartic_moments
    {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K} {Q P : K[X]}
    {U : Submodule K (Fin 24 → K)}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7)
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (five : 5 ≤ (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card) :
    ∃ (q Z : K[X]) (c : Fin 5 → K), Moments q Z c ∧ q.natDegree = 4 := by
  obtain ⟨q, Z, c, M⟩ := width24_weak_five_moments_of_ordinary_head ha ho seven L five
  exact ⟨q, Z, c, M, M.natDegree_eq_four_of_full_packet⟩

end RKResearch.Certified.ERK16
