module

public import RKCert.ReviewedNative.ERK13OrdinaryFirstPort
public import RKCert.ReviewedNative.NativeWeightXSixResidue

@[expose] public section

namespace RKResearch.Certified.Graded.ERK13OrdinaryFirstPort

open RKResearch Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K}
variable {G R Q : K[X]}

/-- Both possible locations of the forced origin factor are excluded for
the supplied clean ordinary head. The producer of that head is separate. -/
theorem CleanHead.impossible (L : CleanHead A U w G R Q)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b) : False :=
  L.impossible_of_cubic_cut ha ho NativeWeightXSix.first_cubic_primitive_nonzero_of_six_moments

end RKResearch.Certified.Graded.ERK13OrdinaryFirstPort
