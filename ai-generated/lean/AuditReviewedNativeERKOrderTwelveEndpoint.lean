module

public import RKCert.ReviewedNative.ERKOrderTwelveEndpoint

public section

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.ERK12

namespace RKResearch.Certified.Graded.AuditERK12Endpoint

/-- Exact reviewed order and physical strictness suffice over arbitrary
characteristic-zero coefficient rings; no field or domain instance is supplied. -/
theorem physical_width_seventeen_impossible {R : Type*} [CommRing R] [CharZero R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 12 A b) (cap : s≤17) : False :=
  (not_le_of_gt (by omega : s<18)) (ho.erk_order_twelve_stages ha)

#print axioms polynomial_degree_cut_at_one
#print axioms probe_mul_clock_polynomial
#print axioms rotated_probe_detects_quotient
#print axioms RankTwoFourProfile.anchored_quotient
#print axioms RankTwoFourProfile.leak_probe_edge
#print axioms exclude_nonzero_rank_two_four
#print axioms RKResearch.HasOrder.erk_order_twelve_stages_field
#print axioms RKResearch.HasOrder.erk_order_twelve_stages
#print axioms physical_width_seventeen_impossible

end RKResearch.Certified.Graded.AuditERK12Endpoint

