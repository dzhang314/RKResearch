import RKCert.ReviewedNative.DIRKOrderTenDirtyInventory

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.CrossedOrderTen
open scoped Matrix

#check dirty_inventory_of_small
#check dirty_first_inventory_of_seven
#check dirty_labels_small_or_high

#print axioms dirty_inventory_of_small
#print axioms dirty_first_inventory_of_seven
#print axioms dirty_labels_small_or_high

example {K : Type*} [Field K] {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}
    (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    (dirtyClockLabels (nodes A) b (monomialStageDefect A 2)).card ≤ 2 ∨
      8 ≤ (dirtyClockLabels (nodes A) b (monomialStageDefect A 2)).card :=
  dirty_labels_small_or_high ha ho
