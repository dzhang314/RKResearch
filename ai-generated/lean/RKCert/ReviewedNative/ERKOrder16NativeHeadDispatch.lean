module

public import RKCert.ReviewedNative.ERKOrder16NativeRankSplit
public import RKCert.ReviewedNative.ERKOrder16WeakContrastCases
public import RKCert.ReviewedNative.ERKOrder16StrongCenteredAdapter

@[expose] public section

/-! # Native head dispatch on the original order-16 width-24 tableau

The returned weak branch keeps one and the same actual head in the
four- or five-site case. The strong branch keeps its physical mask
and all actual ports, with the centered moments on those same rows.
No exclusion of a strong or weak scalar packet is used. -/
namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.ReviewedNative.StrongCentered16

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}

/-- The common returned frame includes the actual first-seed zero,
live terminal, and eighth ranks. No rank, support, or seed hypothesis
is required to select an actual head branch. -/
theorem width24_native_head_dispatch
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
                Moments (Q.comp (1-X)) (nodes A (ι 1)) (nodes A (ι 2)))) := by
  have frame := width24_paid_frame ha ho
  refine ⟨frame, ?_⟩
  rcases width24_seventh_rank_cases_of_frame ha ho frame with seven | eight
  · exact Or.inl ⟨seven, width24_ordinary_weak_contrast_cases ha ho seven⟩
  · obtain ⟨w, g, Q, P, ι, M, B, origin⟩ :=
      width24_strong_actual_ports_and_origin ha ho eight
    exact Or.inr ⟨eight,
      ⟨w, g, Q, P, ι, M, B, origin, M.centered_moments ha ho B origin⟩⟩

end RKResearch.Certified.ERK16
