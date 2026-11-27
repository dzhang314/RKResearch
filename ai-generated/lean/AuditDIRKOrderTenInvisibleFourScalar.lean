import RKCert.ReviewedNative.DIRKOrderTenInvisibleFourScalar

open RKResearch.Certified.Graded.InvisibleFourScalar

#check quartic_roots
#check paid_divisions
#check all_distinct_clock_tuples

#print axioms quartic_roots
#print axioms paid_divisions
#print axioms all_distinct_clock_tuples

example : clockSet.all goodCore = true := all_distinct_clock_tuples
