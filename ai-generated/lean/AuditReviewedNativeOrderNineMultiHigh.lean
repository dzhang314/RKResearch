import RKCert.ReviewedNative.OrderNineMultiSix
open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.OneOff RKResearch.Certified.Graded.MultiOff
#check @order9_exactly_five_off
#check @explicit_order_nine_off_count_ne_five_at_least_thirteen
#print axioms order9_high_off_head_form
#print axioms order9_high_off_terminal
#print axioms order9_no_eight_or_more_off
#print axioms order9_five_on_head_not_dvd
#print axioms order9_no_five_clean_six_or_seven
#print axioms order9_no_seven_off
#print axioms order9_no_six_off_six_on
#print axioms order9_exactly_five_off
#print axioms explicit_order_nine_off_count_ne_five_at_least_thirteen
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 9 A b) (h : (offKnots A).card≠5) :
    13≤s := explicit_order_nine_off_count_ne_five_at_least_thirteen ha ho h
