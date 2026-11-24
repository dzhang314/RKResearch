module

public import RKCert.ReviewedNative.ERKOrder16StrongCenteredAdapter
public import RKCert.ReviewedNative.ERKOrder16StrongCenteredScalar

@[expose] public section

/-! # Exclusion of the actual strong rank-eight width-24 chart -/
namespace RKResearch.Certified.ERK16

open RKResearch Module
open RKResearch.Certified.Graded
open scoped Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}

/-- The actual strong rank-eight chart is impossible. The native paid
frame already earns zero first seed; it is not an extra premise. -/
theorem width24_strong_seventh_rank_ne_eight
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b) :
    finrank K (zeroSpace A 7) ≠ 8 := by
  intro r7
  obtain ⟨q,a,z,h⟩ := width24_strong_centered_moments ha ho r7
  exact RKCert.ReviewedNative.StrongCentered16.not_moments h

end RKResearch.Certified.ERK16
