import RKCert.ExplicitOrderTwelve

open RKCert RKCert.Paired RKCert.Paired.OrderTwelve

#check explicit_order12_ge18_field
#check explicit_order12_ge18_charZero

#print axioms saturation
#print axioms e7_rank
#print axioms mesh_at_end
#print axioms no_double_leak_both
#print axioms saturated_e9_escape
#print axioms RKCert.OrderTwelve.ghost_five_tests_zero
#print axioms RKCert.OrderTwelve.pure_divisor_moment_ne_zero
#print axioms chronological_multiplier_contrast
#print axioms count_by_features
#print axioms off_mask_bootstrap
#print axioms exclude_two_three
#print axioms exclude_two_four
#print axioms no_full_order_twelve_chart
#print axioms explicit_order12_ge18_field
#print axioms explicit_order12_ge18_charZero

-- The checked contradiction addresses actual tableaux, not abstract chart data only.
example {A : Fin 17 → Fin 17 → ℚ} {b : Fin 17 → ℚ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) : False :=
  (by decide : ¬18≤17) (explicit_order12_ge18_field ha ho)

-- Keep the zero-divisor scope visible in an actual specialization.
example {A : Fin 17 → Fin 17 → ℚ × ℚ} {b : Fin 17 → ℚ × ℚ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) : False :=
  (by decide : ¬18≤17) (explicit_order12_ge18_charZero ha ho)

-- The arbitrary nonzero-ring theorem remains independent and is not
-- silently replaced by a theorem requiring characteristic zero.
example {R : Type*} [CommRing R] [Nontrivial R] {n:ℕ}
    {A:Fin n→Fin n→R} {b:Fin n→R} (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) :
    16≤n := uniform_erk_ring ha ho

