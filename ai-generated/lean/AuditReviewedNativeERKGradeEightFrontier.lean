import RKCert.ReviewedNative.ERKGradeEightFrontier
open RKResearch RKResearch.Certified.Graded Module RKCert.Endpoint Polynomial

-- The answer is a hypothesis for later physical geometry, not rank nine by assertion.
example {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 26) (Fin 26) K}
    {b : Fin 26 → K} (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 17)
    (cap : finrank K (zeroSpace A 8)≤8) :
    ∃ r U w, 2≤r ∧ finrank K (zeroSpace A 5)=5 ∧ FlatClockHead A 5 3 r U w :=
  grade_eight_thin_head ha ho (by decide) cap

-- A flat doubling interval for other orders can use the same producer.
example {K : Type*} [Field K] [CharZero K] {s j : ℕ} {A : Matrix (Fin s) (Fin s) K}
    (ha : ∀ i k, i≤k → A i k=0) (hj : 5≤j)
    (sep : ∀ a, coeffEval A (j+j) a ∈ zeroSpace A (j+j) → a=0)
    (cap : finrank K (zeroSpace A (j+j)) ≤ finrank K (zeroSpace A j)+j) :
    ∃ r U w, FlatClockHead A j j r U w :=
  flat_clock_head ha sep (by omega) (by omega) cap

#print axioms RKResearch.Certified.Graded.flat_clock_head
#print axioms RKResearch.Certified.Graded.HeadFiber.faithful_on_escape_sites
#print axioms RKResearch.Certified.Graded.HeadFiber.multiplier_profile_of_chart
#print axioms RKResearch.Certified.Graded.grade_eight_thin_head
#print axioms RKResearch.Certified.Graded.grade_eight_grade_four_split
#print axioms RKResearch.Certified.Graded.grade_eight_grade_three_profile
#print axioms RKResearch.Certified.Graded.grade_eight_core_eq_grade_four
