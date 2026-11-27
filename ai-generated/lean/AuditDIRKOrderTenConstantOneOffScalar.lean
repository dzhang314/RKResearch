import RKCert.ReviewedNative.DIRKOrderTenConstantOneOffScalar

open RKResearch.Certified.Graded.ConstantOneOffScalar

#check jacobi_roots
#check primitive_denominator_units
#check fixed_triples_no_pair_cut
#check fixed_pairs_no_zero_third_head
#check fixed_pairs_no_two_donors
#check all_first_regular_cuts

#print axioms jacobi_roots
#print axioms primitive_denominator_units
#print axioms fixed_triples_no_pair_cut
#print axioms fixed_pairs_no_zero_third_head
#print axioms fixed_pairs_no_two_donors
#print axioms all_first_regular_cuts

example : interior.all (fun τ => interior.all (firstRegularGuard τ)) = true := all_first_regular_cuts
