import RKCert.ReviewedNative.OrderNineOneOffExclusion

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.OneOff
open RKResearch.Certified.Graded.OneOff.Seven
open scoped Matrix Classical

#print axioms order9_forbid_same_clock_interpolation
#print axioms order9_first_five_independent
#print axioms order9_sixth_feature
#print axioms order9_one_off_sixth_chart
#print axioms native_jv_profiles
#print axioms order9_terminal_normal_profile
#print axioms order9_actual_endpoint_chart
#print axioms order9_one_off_two_fibres
#print axioms endBeta_alternatives
#print axioms ordinary_curve
#print axioms order9_last_two_new_on
#print axioms reflected_power_mass
#print axioms reflectedProbe_primitive_of_defect
#print axioms reverse_primitive_paid
#print axioms order9_grade_five_clock_noninvariant
#print axioms order9_native_profiles
#print axioms order9_actual_tail_identities
#print axioms tail_hankel_collision
#print axioms tail_cubic_impossible
#print axioms tail_quartic_impossible
#print axioms order9_one_off_impossible
#print axioms explicit_order_nine_one_off_at_least_thirteen
#print axioms RKCert.Paired.OneOff.endpoint_nonzero
#print axioms RKCert.Paired.OneOff.cubic_tail_mass
#print axioms RKCert.Paired.OneOff.four_root_tail_hankel
#print axioms RKCert.Paired.reflected_collision_scalar

-- Independent consumer: the reviewed tableau and HasOrder are not converted.
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder A b 9)
    (off : (offKnots A).card = 1) : 13 ≤ s :=
  explicit_order_nine_one_off_at_least_thirteen ha ho off
