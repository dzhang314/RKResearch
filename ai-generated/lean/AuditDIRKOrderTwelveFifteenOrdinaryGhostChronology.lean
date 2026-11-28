import RKCert.ReviewedNative.DIRKOrderTwelveFifteenOrdinaryGhostChronology

open RKResearch.Certified.Graded.OrderTwelveFifteen.OrdinaryGhostChronology

example {K : Type*} [Field K] [CharZero K] (a b beta M : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a-b ≠ 0)
    (hU : M*(f a b-beta*(b-a)*s a b)=beta^2*(b-a)*s a b)
    (hW : M*(ell a b-beta*j a b)=beta^2*j a b) :
    beta=0 := secondDiagonal a b beta M ha hb hab hU hW

example {K : Type*} [Field K] [CharZero K] (a b z delta : K)
    (hb : b ≠ 0) (hba : b-a ≠ 0) (hd : delta=b-z)
    (h : (z-a-delta)*ell a b=delta*f a b) :
    (6*b-3*a)*z=b*(5*b-2*a) := fourthClock a b z delta hb hba hd h

example {K : Type*} [Field K] [CharZero K] (x z : K)
    (hz : 3*(2*x-1)*z=x*(5*x-2)) :
    60*(2*x-1)*(jx₂ 1 x-j 1 x-(z+1)*f 1 x)
      = x^4*(2*x^2-6*x+5) := gradeSixCoefficient x z hz

#print axioms primitiveDeterminant
#print axioms secondDiagonal
#print axioms noLateCubicFit
#print axioms fourthClock
#print axioms gradeSixCoefficient
#print axioms zeroGhostQuintic
