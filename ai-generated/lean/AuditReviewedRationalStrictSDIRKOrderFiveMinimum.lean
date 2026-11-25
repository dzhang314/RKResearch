module

import RKCert.ReviewedNative.RationalStrictSDIRKOrderFiveMinimum

open RKResearch.Certified

example : IsLeast (rationalStrictSDIRKStages 5) 5 :=
  rational_strictSDIRK_five_minima.1

example : IsLeast (rationalStrictSDIRKExactStages 5) 5 :=
  rational_strictSDIRK_five_minima.2

#print axioms rational_strictSDIRK_five_minima
