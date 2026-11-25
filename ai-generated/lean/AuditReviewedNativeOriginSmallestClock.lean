import RKCert.ReviewedNative.OrderedOriginPositiveClock
import RKCert.ReviewedNative.OrderedOriginSmallestClock

open Polynomial RKCert.ReviewedNative.OriginSignedSquares

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example : NoSmallestClock K := noSmallestClock_of_pole_sign_cuts

example {P : K[X]} {u v w : K} (H : TwoSidedThreeClockMoments P u v w) : False :=
  H.impossible_of_positive_and_not_smallest positiveFirstClock_of_finite_sign
    noSmallestClock_of_pole_sign_cuts

end

#print axioms RKCert.ReviewedNative.OriginSignedSquares.noSmallestClock_of_pole_sign_cuts
#print axioms RKCert.ReviewedNative.OriginSignedSquares.TwoSidedThreeClockMoments.impossible_of_positive_and_not_smallest
