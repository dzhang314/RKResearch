import RKCert.ReviewedNative.OrderNineExplicitThirteen

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.OneOff RKResearch.Certified.Graded.MultiOff

#check @order9_actual_five_six_FG
#check @ActualSixOnFG.compatibility_zero
#check @order9_actual_five_six_atlas_input
#check @order9_no_five_off_six_on
#check @explicit_order_nine_at_least_thirteen

#print axioms order9_five_six_stage_chart
#print axioms order9_five_six_ten_distinct_prefix
#print axioms order9_five_six_late_rows
#print axioms order9_actual_five_six_FG
#print axioms ActualSixOnFG.compatibility_zero
#print axioms order9_actual_quadratic_first_on_fifth_or_sixth
#print axioms order9_actual_five_six_on_eighth_two_step
#print axioms order9_actual_five_six_on_eighth_atlas
#print axioms order9_actual_five_six_quartic_remainders
#print axioms order9_actual_five_six_off_eighth
#print axioms ActualSixOnFG.terminal_product_zero
#print axioms order9_actual_five_six_atlas_input
#print axioms RKCert.CompactResidue.sixOn_atlas_impossible
#print axioms order9_no_five_off_six_on
#print axioms explicit_order_nine_at_least_thirteen

-- An independent consumer with just the reviewed order and strict explicitness.
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder A b 9) :
    13 ≤ s :=
  explicit_order_nine_at_least_thirteen ha ho
