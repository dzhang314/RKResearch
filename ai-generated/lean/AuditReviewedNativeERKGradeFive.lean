module
import RKCert.ReviewedNative.ERKGradeFiveSurplus

open RKResearch RKResearch.Certified.Graded Module
#check @grade_five_surplus
#check @grade_five_surplus_of_reviewed_order
#check @order15_ordinary_forward_head
#print axioms PolySeparated.coeff
#print axioms minimal_grade_five_ranks
#print axioms minimum_five_clock_step
#print axioms origin_of_dependent_quadratic
#print axioms constant_amplitude_of_grade_five_dependence
#print axioms OneOff.GlobalNormal.five_defect_of_minrank
#print axioms OneOff.GlobalNormal.disjoint_defects_of_minimal_five
#print axioms grade_five_surplus_of_dependent_quadratic
#print axioms explicit_order_on_first_profiles
#print axioms clean_five_receiver_profile_floor
#print axioms primitive_X_mul_no_nonzero_root
#print axioms grade_five_surplus_of_independent_quadratic
#print axioms grade_five_surplus
#print axioms grade_five_surplus_of_reviewed_order
#print axioms order15_ordinary_forward_head

/-- Public consumer with only one import, using no assumed defect rank. -/
example {K : Type*} [Field K] [CharZero K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} {b : Fin n→K}
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder A b 15) (cap : n≤22) :
    n=22 := (order15_ordinary_forward_head ha ho cap).1
