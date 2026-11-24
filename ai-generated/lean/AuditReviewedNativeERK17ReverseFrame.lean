import RKCert.ReviewedNative.ERK17ReverseSupport

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.ERK17 Module Polynomial
open RKCert.Endpoint.WeightedClock

example {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}
    {b : Fin s → K} (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 17 A b) : 25≤s :=
  order17_width_floor25 ha ho

example {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 26) (Fin 26) K}
    {b : Fin 26 → K} (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 17 A b)
    (middle : 9≤finrank K (zeroSpace A 8)) (nonzero : firstSeed A b≠0) :
    (weightedSites (reflectedClock A) (firstSeed A b)).card ≤ 2 ∨ WideLinear A b :=
  width26_linear_broad_or_local ha ho (width26_frame ha ho middle) nonzero

#print axioms RKResearch.Certified.Graded.Reverse.reverse_clock_invariant_gain
#print axioms RKCert.Endpoint.WeightedClock.weightedBand_eq_range
#print axioms RKResearch.Certified.ERK17.order17_width_floor25
#print axioms RKResearch.Certified.ERK17.width26_seed_split
#print axioms RKResearch.Certified.ERK17.width26_reverse_clock_escape
#print axioms RKResearch.Certified.ERK17.width26_linear_broad_or_local
#print axioms RKResearch.Certified.ERK17.width26_quadratic_wide_of_two_sites
