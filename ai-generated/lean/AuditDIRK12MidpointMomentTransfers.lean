import RKCert.ReviewedNative.DIRK12MidpointMomentTransfers

open RKResearch.Certified.DIRK12MidpointMomentTransfers

example {K : Type} [CommRing K] {a b c y : K} (h : cubic a b c y = 0) :
    -mk a b c y*j60 a b c y = affine60 a b c y :=
  affine_at_root h

example {K : Type} [CommRing K] (a b c d e : K) :
    5*((b*c)*d-C (a*c) (b*b)*e)-6*(a*c-b*b)*e = -rel4 a b c d e :=
  paid_pair3 a b c d e

#print axioms RKResearch.Certified.DIRK12MidpointMomentTransfers.affine_at_root
#print axioms RKResearch.Certified.DIRK12MidpointMomentTransfers.paid_hull0
#print axioms RKResearch.Certified.DIRK12MidpointMomentTransfers.paid_hull1
#print axioms RKResearch.Certified.DIRK12MidpointMomentTransfers.paid_pair3
