import RKCert.ReviewedNative.ERK8FourOffCleanPlacementAdapter

open Polynomial RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.OneOff RKResearch.Certified.Graded.FourOffPhysical
open RKResearch.Certified.Graded.FourOffNewton
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open scoped Matrix

namespace RK8CleanPlacementAdapterAudit

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The exact arguments of terminal_profile_shape_and_hull, except that
the unpaid terminal/shape/Newton modules are intentionally not imported. -/
theorem exact_k_six_seven
    (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10 → K)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (off : (offKnots A).card=4) :
    ∃ (P : K[X]) (i k : Fin 10), Placement A b P i k ∧
      CleanPrimitivePlacement A b k 6 (nodes A 7) :=
  paired_placements_of_order8_four_off ha ho off

end RK8CleanPlacementAdapterAudit

#print axioms RKResearch.Certified.Graded.FourOffNewton.marked_clean_value_census
#print axioms RKResearch.Certified.Graded.FourOffNewton.marked_paid_clean_cubic
#print axioms RKResearch.Certified.Graded.FourOffNewton.marked_actual_clean_geometry
#print axioms RKResearch.Certified.Graded.FourOffNewton.clean_primitive_placement_of_marked
#print axioms RKResearch.Certified.Graded.FourOffNewton.paired_placements_of_order8_four_off
#print axioms RK8CleanPlacementAdapterAudit.exact_k_six_seven
