import RKCert.ReviewedNative.ERKOrder15PaidQuarticCut

open RKResearch RKResearch.Certified.Graded
open Polynomial

/-- The checked result uses the reviewed order predicate without conversion. -/
theorem audit_native_order15_rank_two {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 15 A b) (cap : s+1≤22) :
    ∃ (a : ℕ) (G : K[X]) (U : Submodule K (Fin (s+1)→K)) (w : Fin (s+1)→K),
      Order15PaidStaircase A b a G 2 U w :=
  order15_rank_two_staircase ha ho cap

#print axioms RKResearch.Certified.Graded.physical_head_knot
#print axioms RKResearch.Certified.Graded.physical_head_knots_three_two
#print axioms RKResearch.Certified.Graded.PhysicalHeadKnots.complementary_roots
#print axioms RKResearch.Certified.Graded.marked_defect_mat
#print axioms RKResearch.Certified.Graded.weighted_eval_mem_of_powers
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.large_head_knot
#print axioms RKCert.EndpointPhysical.formalPrimitive_moment
#print axioms RKCert.EndpointPhysical.tests_of_primitives
#print axioms RKCert.EndpointPhysical.cubic_eq_zero_of_primitives
#print axioms RKCert.EndpointPhysical.ordered_quartic_eq_zero_of_primitives
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.large_head_complementary_knots
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.head_eq_two
#print axioms RKResearch.Certified.Graded.order15_rank_two_staircase
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.terminal_of_paid_quartic
#print axioms RKCert.EndpointPhysical.normalize
#print axioms RKCert.Endpoint.match3
#print axioms RKCert.Endpoint.ordered_quartic_three_two
#print axioms RKResearch.Certified.Graded.LiveCore.exists_live_indicator
#print axioms audit_native_order15_rank_two
