module

import RKCert.ReviewedNative.RationalStrictSDIRKOrderSixMinimum

open RKResearch.Certified

example : IsLeast (rationalStrictSDIRKStages 6) 7 :=
  rational_strictSDIRK_six_minima.1

example : IsLeast (rationalStrictSDIRKExactStages 6) 7 :=
  rational_strictSDIRK_six_minima.2

#print axioms rational_strictSDIRK_six_minima
