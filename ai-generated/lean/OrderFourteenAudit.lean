import RKCert.ExplicitOrderFourteen
import RKCert.OrderedIntervalMoments

open RKCert RKCert.Paired

#check explicit_order14_ge21_field
#check explicit_order14_ge21_charZero
#check explicit_order14_ge21_orderedField
#print axioms explicit_order14_ge21_field
#print axioms explicit_order14_ge21_charZero
#print axioms explicit_order14_ge21_orderedField

example {K : Type*} [Field K] [CharZero K]
    {A : Fin 20 → Fin 20 → K} {b : Fin 20 → K}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 14) : False := by
  have h := explicit_order14_ge21_field ha ho
  omega

example {R : Type*} [CommRing R] [CharZero R]
    {A : Fin 20 → Fin 20 → R} {b : Fin 20 → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 14) : False := by
  have h := explicit_order14_ge21_charZero ha ho
  omega

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Fin 20 → Fin 20 → K} {b : Fin 20 → K}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 14) : False := by
  have h := explicit_order14_ge21_orderedField ha ho
  omega

#print axioms FiniteMidpoint.saturated_short
#print axioms FiniteMidpoint.even_seven_chart
#print axioms FiniteMidpoint.even_seven_leak_free
#print axioms FiniteMidpoint.even_seven_profile
#print axioms FiniteMidpoint.physical_seven_knot
#print axioms FiniteMidpoint.fixed14_divisor_nonzero
#print axioms FiniteMidpoint.seven_terminal_factors
#print axioms FiniteMidpoint.cubic_from_seven_masks
#print axioms OrderedGram.cauchyForm_pos
#print axioms OrderedGram.pow_square_pos
#print axioms OrderedGram.interval_square_pos
#print axioms OrderedGram.ordered_anchored_separation
