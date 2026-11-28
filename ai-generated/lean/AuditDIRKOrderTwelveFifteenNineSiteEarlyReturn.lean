import RKCert.ReviewedNative.DIRKOrderTwelveFifteenNineSiteEarlyReturn

open RKResearch.Certified.Graded.OrderTwelveFifteen.NineSiteEarlyReturn

example {K : Type*} [Field K] [CharZero K] (d v td tv : K)
    (hd : d ≠ 0) (hv : v ≠ 0) (hvd : v-d ≠ 0)
    (h₁ : d*td+v*tv=d^2/2) (h₂ : d^2*td+v^2*tv=d^3/2) :
    tv=0 ∧ td=d/2 := uniformReturn d v td tv hd hv hvd h₁ h₂

example {K : Type*} [Field K] [CharZero K] (r t h : K)
    (hr₁ : r-1 ≠ 0) (hr₂ : r-2 ≠ 0) (hrh : 2*r-1 ≠ 0)
    (ht₀ : t ≠ 0) (ht₁ : t-1 ≠ 0) (hrt : r-t ≠ 0)
    (e : aCoef r t*h+bCoef r t=0)
    (f : q₂ r t*h^2+q₁ r t*h+q₀ r t=0) :
    (r^2-4*r+1)*t+r*(r+1) = 0 :=
  thirdRatio r t h hr₁ hr₂ hrh ht₀ ht₁ hrt e f

#print axioms uniformReturn
#print axioms zeroReceiver
#print axioms resultantIdentity
#print axioms thirdRatio
