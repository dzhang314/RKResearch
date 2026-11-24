import RKCert.ReviewedNative.OrderNineFiveFiveExclusion
open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.OneOff RKResearch.Certified.Graded.MultiOff
#check @order9_no_five_off_five_on
#check @order9_five_six_remaining
#check @explicit_order_nine_outside_five_six_at_least_thirteen
#print axioms orderAdjoint_annih
#print axioms state_defect_five_zero_on
#print axioms order9_five_off_five_on_rank_nine_impossible
#print axioms order9_ten_distinct_prefix_full
#print axioms gather_adjoint_by_row_difference
#print axioms order9_fixed_radau_late_data
#print axioms order9_no_five_off_five_on
#print axioms order9_five_six_remaining
#print axioms explicit_order_nine_outside_five_six_at_least_thirteen
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 9 A b)
    (outside : ¬ ((offKnots A).card=5 ∧ (cleanKnots A).card=6)) : 13≤s :=
  explicit_order_nine_outside_five_six_at_least_thirteen ha ho outside
