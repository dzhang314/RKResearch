import RKCert.ReviewedNative.SmallSDIRKRealAlgebraic

open RKResearch RKResearch.Certified

#check hasOrder_of_finite_residual_dvd
#check NorsettCrouzeix23.order_three
#check NorsettCrouzeix23.fourth_chain_scaled
#check NorsettCrouzeix23.not_order_four
#check NorsettCrouzeix23.real_root
#check NorsettCrouzeix23.algebraic_root
#check Crouzeix34.order_four
#check Crouzeix34.outerWeight_eq_fraction
#check Crouzeix34.fifth_bush_scaled
#check Crouzeix34.not_order_five
#check Crouzeix34.real_root
#check Crouzeix34.algebraic_root
#check exists_strictSDIRK_exact_three_realAlgebraic
#check exists_strictSDIRK_exact_four_realAlgebraic

-- These are genuinely coefficients in a subfield of the reals, not only
-- an abstract field with formal roots of the two defining polynomials.
example (x : algebraicClosure ℚ ℝ) : IsAlgebraic ℚ (x : ℝ) :=
  mem_algebraicClosure_iff.mp x.property

#print axioms hasOrder_of_finite_residual_dvd
#print axioms NorsettCrouzeix23.order_three
#print axioms NorsettCrouzeix23.not_order_four
#print axioms NorsettCrouzeix23.real_root
#print axioms NorsettCrouzeix23.algebraic_root
#print axioms Crouzeix34.order_four
#print axioms Crouzeix34.outerWeight_eq_fraction
#print axioms Crouzeix34.not_order_five
#print axioms Crouzeix34.real_root
#print axioms Crouzeix34.algebraic_root
#print axioms exists_strictSDIRK_exact_three_realAlgebraic
#print axioms exists_strictSDIRK_exact_four_realAlgebraic
