import RKCert.ReviewedNative.CooperSayfy55Real

open RKResearch RKResearch.Certified

-- The complete finite enumerator has exactly these ordered encodings.
example : (List.range 5).map (fun n => (treesOfOrderSucc n).length) = [1, 1, 2, 5, 14] := by
  decide +kernel

#check CooperSayfy55.row_sums
#check CooperSayfy55.lowerTriangular
#check CooperSayfy55.diagonal
#check CooperSayfy55.order_five
#check CooperSayfy55.sixth_bush_scaled
#check CooperSayfy55.not_order_six
#check CooperSayfy55.specialize_coeff
#check CooperSayfy55.specialize_gamma
#check CooperSayfy55.specialized_exact
#check CooperSayfy55.real_root
#check CooperSayfy55.algebraic_root
#check exists_strictSDIRK_exact_five_realAlgebraic
#check exists_strictSDIRK_exact_five_real

#print axioms CooperSayfy55.order_five
#print axioms CooperSayfy55.sixth_bush_scaled
#print axioms CooperSayfy55.specialized_exact
#print axioms CooperSayfy55.real_root
#print axioms CooperSayfy55.algebraic_root
#print axioms exists_strictSDIRK_exact_five_realAlgebraic
#print axioms exists_strictSDIRK_exact_five_real
