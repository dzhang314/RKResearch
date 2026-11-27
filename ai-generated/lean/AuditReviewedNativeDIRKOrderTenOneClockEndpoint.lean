import RKCert.ReviewedNative.DIRKOrderTenOneClockEndpoint

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.OneClockEndpointDebit
open RKResearch.Certified.Graded.CrossedOrderTen.OneClockEndpoint
open scoped Matrix

#check exists_endpoint_debited_support
#check small_support_polynomial_test
#check endpoint_debit_closes_power_tests
#check simple_pole_clears
#check double_pole_clears
#check terminal_coordinate_mem
#check terminal_weight_eq
#check fiberMass_remove_dark
#check dirty_pair_has_zero_fibers
#check dark_rows_ordinary_measure_eq
#check cancelled_pair_measure_eq_of_scaled11
#check three_dark_rows_measure_eq_of_simple_pole
#check cancelled_pair_measure_eq_of_double_pole

#print axioms exists_endpoint_debited_support
#print axioms small_support_polynomial_test
#print axioms endpoint_debit_closes_power_tests
#print axioms simple_pole_clears
#print axioms double_pole_clears
#print axioms terminal_coordinate_mem
#print axioms terminal_weight_eq
#print axioms fiberMass_remove_dark
#print axioms dirty_pair_has_zero_fibers
#print axioms dark_rows_ordinary_measure_eq
#print axioms cancelled_pair_measure_eq_of_scaled11
#print axioms three_dark_rows_measure_eq_of_simple_pole
#print axioms cancelled_pair_measure_eq_of_double_pole

section Typed
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}
example (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (clean : ∀ f∈zeroSpace A 5, f (Fin.last 10)=0) :
    b (Fin.last 10)=(1:K)/30 := terminal_weight_eq ha ho clean
end Typed
