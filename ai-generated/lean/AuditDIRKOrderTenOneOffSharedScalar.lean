import RKCert.ReviewedNative.DIRKOrderTenOneOffSharedScalar

open RKResearch.Certified.Graded.OneOffSharedScalar

#check jacobi_roots
#check paid_divisor_guards
#check fixed_pair_guards
#check all_off_core_cuts
#check all_off_head_cuts

#print axioms jacobi_roots
#print axioms paid_divisor_guards
#print axioms fixed_pair_guards
#print axioms all_off_core_cuts
#print axioms all_off_head_cuts

example : interior.all (fun τ => interior.all (fun x => if τ=x then true else tupleGood true τ x)) = true :=
  all_off_core_cuts

example : interior.all (fun τ => interior.all (fun x => if τ=x then true else tupleGood false τ x)) = true :=
  all_off_head_cuts
