import RKCert.ExplicitFiniteERK16to19

open RKCert RKCert.Paired

#check explicit_order16_ge24_field
#print axioms explicit_order16_ge24_field
#check explicit_order16_ge24_charZero
#print axioms explicit_order16_ge24_charZero

example {K : Type*} [Field K] [CharZero K]
    {A : Fin 23 → Fin 23 → K} {b : Fin 23 → K}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 16) : False := by
  have h := explicit_order16_ge24_field ha ho
  omega

example {R : Type*} [CommRing R] [CharZero R]
    {A : Fin 23 → Fin 23 → R} {b : Fin 23 → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 16) : False := by
  have h := explicit_order16_ge24_charZero ha ho
  omega

#check explicit_order17_ge26_field
#print axioms explicit_order17_ge26_field
#check explicit_order17_ge26_charZero
#print axioms explicit_order17_ge26_charZero

example {K : Type*} [Field K] [CharZero K]
    {A : Fin 25 → Fin 25 → K} {b : Fin 25 → K}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 17) : False := by
  have h := explicit_order17_ge26_field ha ho
  omega

example {R : Type*} [CommRing R] [CharZero R]
    {A : Fin 25 → Fin 25 → R} {b : Fin 25 → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 17) : False := by
  have h := explicit_order17_ge26_charZero ha ho
  omega

#check explicit_order18_ge27_field
#print axioms explicit_order18_ge27_field
#check explicit_order18_ge27_charZero
#print axioms explicit_order18_ge27_charZero

example {K : Type*} [Field K] [CharZero K]
    {A : Fin 26 → Fin 26 → K} {b : Fin 26 → K}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 18) : False := by
  have h := explicit_order18_ge27_field ha ho
  omega

example {R : Type*} [CommRing R] [CharZero R]
    {A : Fin 26 → Fin 26 → R} {b : Fin 26 → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 18) : False := by
  have h := explicit_order18_ge27_charZero ha ho
  omega

#check explicit_order19_ge29_field
#print axioms explicit_order19_ge29_field
#check explicit_order19_ge29_charZero
#print axioms explicit_order19_ge29_charZero

example {K : Type*} [Field K] [CharZero K]
    {A : Fin 28 → Fin 28 → K} {b : Fin 28 → K}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 19) : False := by
  have h := explicit_order19_ge29_field ha ho
  omega

example {R : Type*} [CommRing R] [CharZero R]
    {A : Fin 28 → Fin 28 → R} {b : Fin 28 → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 19) : False := by
  have h := explicit_order19_ge29_charZero ha ho
  omega

#print axioms FiniteMidpoint.explicit_finite_floor_field
#print axioms FiniteMidpoint.actual_chart
#print axioms FiniteMidpoint.chart_sites
#print axioms FiniteMidpoint.leak_free
#print axioms FiniteMidpoint.physical_profile
#print axioms FiniteMidpoint.physical_knot
#print axioms FiniteMidpoint.actual_two_knots
#print axioms FiniteMidpoint.q9_no_profile
#print axioms FiniteMidpoint.free_pencil_factor
#print axioms FiniteMidpoint.prefix8_no_profile

