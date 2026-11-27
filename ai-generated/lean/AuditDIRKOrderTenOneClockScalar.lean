import RKCert.ReviewedNative.DIRKOrderTenOneClockScalar

open RKResearch.Certified.Graded.OneClockScalar

#check jacobiFour_roots
#check all_lobatto_triples
#check all_lobatto_two_donor_tests
#check all_lobatto_three_donor_tests
#check all_lobatto_three_label_denominators
#check all_lobatto_two_label_guards
#check all_lobatto_one_off_five_taps

#print axioms jacobiFour_roots
#print axioms all_lobatto_triples
#print axioms all_lobatto_two_donor_tests
#print axioms all_lobatto_three_donor_tests
#print axioms all_lobatto_three_label_denominators
#print axioms all_lobatto_two_label_guards
#print axioms all_lobatto_one_off_five_taps

example : nonzeroLobatto.all (fun a => nonzeroLobatto.all (fun b => nonzeroLobatto.all (tupleNonzero a b))) = true :=
  all_lobatto_triples
