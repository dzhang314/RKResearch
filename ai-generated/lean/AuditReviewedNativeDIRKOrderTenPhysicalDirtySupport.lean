import RKCert.ReviewedNative.DIRKOrderTenPhysicalDirtySupport

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.CrossedOrderTen
open RKCert.Endpoint.WeightedClock
open scoped Matrix

example {K : Type*} [Field K] [CharZero K]
    {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}
    (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    let d := (weightedSites (nodes A) (monomialStageDefect A 2)).card
    d ≠ 2 ∧ d ≠ 3 :=
  physical_dirty_count_ne_two_three ha ho

example {A : Matrix (Fin 11) (Fin 11) ℚ} {b : Fin 11 → ℚ}
    (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    (weightedSites (nodes A) (monomialStageDefect A 2)).card = 1 ∨
      4 ≤ (weightedSites (nodes A) (monomialStageDefect A 2)).card :=
  physical_dirty_count_one_or_at_least_four ha ho

#print axioms physical_dirty_count_ne_two_three
#print axioms physical_dirty_count_one_or_at_least_four
