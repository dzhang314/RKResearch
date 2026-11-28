import RKCert.ReviewedNative.DIRKOrderTwelveFifteenNoLateAffineMasks

open RKResearch.Certified.Graded.OrderTwelveFifteen.NoLateAffineMasks

example {K : Type*} [Field K] (x d p : K) (hx : x ≠ 0) (hx₁ : x-1 ≠ 0)
    (hp : 2*(5*x-3)*p+x^4*((6*x-10)*d-x+1)=0)
    (hr : (2*x-1)*(x-1-d)*p+d^2*x^4*(2*x^2-6*x+5)=0) :
    20*(x-1)^2*d^2+(-12*x^2+24*x-9)*d+2*x^2-3*x+1=0 :=
  diagonalProjection x d p hx hx₁ hp hr

example {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (x d : L)
    (h : 20*(x-1)^2*d^2+(-12*x^2+24*x-9)*d+2*x^2-3*x+1=0) :
    0 ≤ -(2*x-1)*(8*x^3+12*x^2-30*x+1) :=
  discrimNonnegative x d h

#print axioms acFactor
#print axioms tapRelation
#print axioms diagonalProjection
#print axioms implicitFirst
#print axioms discrimNonnegative
