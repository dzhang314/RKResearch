import RKCert.ReviewedNative.OrderNineMultiLow
import RKCert.ReviewedNative.OrderNineMultiScalar

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.OneOff RKResearch.Certified.Graded.MultiOff
#check @order9_low_census
#check @order9_multi_quadrature
#check @explicit_order_nine_at_most_four_off_at_least_thirteen
#check @six_on_witness_impossible
#print axioms not_two_or_three
#print axioms two_curve_head
#print axioms order9_multi_quadrature
#print axioms order9_on_count_le_six
#print axioms grade_five_not_stable
#print axioms order9_no_four_off_nodes
#print axioms order9_low_census
#print axioms order9_at_least_five_off
#print axioms explicit_order_nine_at_most_four_off_at_least_thirteen
#print axioms six_on_witness_impossible
#print axioms RKCert.CompactResidue.sixOn_atlas_impossible

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 9) (few : (offKnots A).card≤4) :
    13≤s := explicit_order_nine_at_most_four_off_at_least_thirteen ha ho few
