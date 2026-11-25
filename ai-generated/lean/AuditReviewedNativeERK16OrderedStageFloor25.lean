module

import RKCert.ReviewedNative.ERKOrder16OrderedStageFloor25

namespace RKCert.Audit.ERK16OrderedStageFloor25

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Audit the exported width-24 theorem at the reviewed tableau predicate. -/
theorem exact_width24_type {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
    (strict : ∀ i j, i ≤ j → A i j = 0) (order : RKResearch.HasOrder 16 A b) : False :=
  RKResearch.Certified.ERK16.ordered_erk16_width24_impossible strict order

/-- Audit the exported all-width result, without any scalar callback. -/
theorem exact_stage_floor_type {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (strict : ∀ i j, i ≤ j → A i j = 0) (order : RKResearch.HasOrder 16 A b) : 25 ≤ s :=
  RKResearch.Certified.ERK16.ordered_erk16_stage_floor25 strict order

#check @RKResearch.Certified.ERK16.ordered_erk16_width24_impossible
#check @RKResearch.Certified.ERK16.ordered_erk16_stage_floor25
#print axioms RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells.no_actual_sole_inner
#print axioms RKCert.ReviewedNative.ThreeInteriorPencil.no_actual_threeInterior_of_literal_table
#print axioms RKResearch.Certified.ERK16.ordered_erk16_width24_impossible
#print axioms RKResearch.Certified.ERK16.ordered_erk16_stage_floor25

end RKCert.Audit.ERK16OrderedStageFloor25
