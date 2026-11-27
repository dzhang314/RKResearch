import RKCert.ReviewedNative.DIRKOrderTenAllFixedPrefixScalar

open RKResearch.Certified.Graded.OneOffSharedScalar
open RKResearch.Certified.Graded.AllFixedPrefixScalar

#check jacobi_roots
#check paid_divisor_guards
#check other_interior_taps_nonzero
#check all_first_change_guards

#print axioms other_interior_taps_nonzero
#print axioms all_first_change_guards

example : interior.all (fun ξ => interior.all (fun a => interior.all (fun b =>
    interior.all (validInteriorCase ξ a b)))) = true := all_first_change_guards
