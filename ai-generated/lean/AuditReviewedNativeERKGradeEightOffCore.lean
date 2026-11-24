import RKCert.ReviewedNative.ERKGradeEightOffCore

open RKResearch RKResearch.Certified.Graded Module Polynomial

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 17 A b)
    (small : finrank K (zeroSpace A 8)≤8) :
    finrank K (zeroSpace A 4)=4 ∧ ∃ r U w, FlatClockHead A 4 4 r U w :=
  ordered_grade_eight_quartic_only ha ho (by decide) small

#print axioms RKResearch.Certified.Graded.LiveCore.exists_live_indicator
#print axioms RKResearch.Certified.Graded.LiveCore.live_sites_le_rank_of_indicator
#print axioms RKResearch.Certified.Graded.rank_three_off_core_clocks
#print axioms RKResearch.Certified.Graded.no_rank_three_clock_core_at_order_ten
#print axioms RKResearch.Certified.Graded.ordered_grade_eight_quartic_only
