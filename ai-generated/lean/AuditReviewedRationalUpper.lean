import RKCert.ReviewedNative.RationalUpper

open RKResearch RKResearch.Certified

-- Exact-size enumeration of the plane binary encodings used by the reviewed tree.
example : (List.range 7).map (fun k => (treesOfOrderSucc k).length) = [1,1,2,5,14,42,132] := by
  decide +kernel

-- Check that the executable checker rejects each next order too.
example : checkOrder ClassicalRK4.A ClassicalRK4.b 5 = false := by decide +kernel
example : checkOrder ImplicitMidpoint.A ImplicitMidpoint.b 3 = false := by decide +kernel
example : checkOrder MidpointExtrapolation4.A MidpointExtrapolation4.b 5 = false := by decide +kernel

#check mem_treesOfOrderSucc
#check checkOrder_iff
#check ClassicalRK4.explicit
#check ClassicalRK4.order_four
#check ClassicalRK4.fifth_bush_value
#check ClassicalRK4.not_order_five
#check ImplicitMidpoint.lowerTriangular
#check ImplicitMidpoint.common_diagonal
#check ImplicitMidpoint.diagonal_ne_zero
#check ImplicitMidpoint.order_two
#check ImplicitMidpoint.third_bush_value
#check ImplicitMidpoint.not_order_three
#check MidpointExtrapolation4.lowerTriangular
#check MidpointExtrapolation4.not_common_diagonal
#check MidpointExtrapolation4.order_four
#check MidpointExtrapolation4.fifth_bush_value
#check MidpointExtrapolation4.not_order_five
#print axioms mem_treesOfOrderSucc
#print axioms checkOrder_iff
#print axioms ClassicalRK4.order_four
#print axioms ClassicalRK4.not_order_five
#print axioms ImplicitMidpoint.order_two
#print axioms ImplicitMidpoint.not_order_three
#print axioms MidpointExtrapolation4.order_four
#print axioms MidpointExtrapolation4.not_order_five
