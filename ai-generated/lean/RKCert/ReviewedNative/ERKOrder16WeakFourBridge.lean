module

public import RKCert.ReviewedNative.ERKOrder16WeakContrastCases
public import RKCert.ReviewedNative.ERKOrder16WeakFourPorts

@[expose] public section

/-! # Paid weak-four chronology on the dispatcher’s actual weak head -/
namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint.WeightedClock

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
variable {U : Submodule K (Fin 24 → K)} {w : Fin 24 → K} {Q P : K[X]}

/-- Consume the exact trace fits of the same weak head. Four numerical
sites need not be four physical rows. The two witnesses are original
rows in their checked chronological order. -/
theorem Width24OrdinaryWeakHead.weak_four_actual_ports
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (four : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4) :
    ∃ (Z : K[X]) (i j : Fin 24), j < i ∧ reverseContrast A b Q P i ≠ 0 ∧
      reverseContrast A b Q P j ≠ 0 ∧
      WeakFourChronologicalPorts Q Z (reflectedClock A i) (reflectedClock A j) :=
  native_width24_weak_four_extra_port ha ho L.qDegree L.pDegree L.qFit L.pFit four

/-- Package the four-site payments directly on the checked weak split.
The five-site alternative is returned unchanged, with the same head. -/
theorem width24_ordinary_weak_contrast_cases_with_four_ports
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7) :
    ∃ (U : Submodule K (Fin 24 → K)) (w : Fin 24 → K) (Q P : K[X]),
      Width24OrdinaryWeakHead A b U w Q P ∧
        (((weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4 ∧
          (∃ (Z : K[X]) (i j : Fin 24), j < i ∧ reverseContrast A b Q P i ≠ 0 ∧
            reverseContrast A b Q P j ≠ 0 ∧
            WeakFourChronologicalPorts Q Z (reflectedClock A i) (reflectedClock A j))) ∨
         (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 5) := by
  obtain ⟨U,w,Q,P,L,split⟩ := width24_ordinary_weak_contrast_cases ha ho seven
  rcases split with four | five
  · exact ⟨U,w,Q,P,L,Or.inl ⟨four,L.weak_four_actual_ports ha ho four⟩⟩
  · exact ⟨U,w,Q,P,L,Or.inr five⟩

end
end RKResearch.Certified.ERK16
