import RKCert.ReviewedNative.DIRKOrderTwelveFifteenFourthMaskCore

open RKResearch.Certified.Graded.OrderTwelveFifteen.FourthMaskCore

example (beta step gap ell slope chi big diag : Int)
    (hstep : step ≠ 0) (hgap : gap ≠ 0) (hbig : big ≠ 0)
    (row : step*ell=beta*diag)
    (top : beta=0 → chi*big=slope)
    (compare : beta=0 → ell=0 → slope*gap=0)
    (unitCase : slope=0 → chi≠0) : beta≠0 :=
  betaGuard beta step gap ell slope chi big diag hstep hgap hbig row top compare unitCase

example (num den coeff : Int) (hden : den≠0)
    (cleared : (den+num)*coeff=num*coeff) : coeff=0 :=
  leadingSlopeCancellation num den coeff hden cleared

example :
    check 19 24 (prod A6 S6 4 + prod B6 T6 4)
                 (pack f6*pack [16, 5, 4, 7, 15, 18, 1, 8, 14, 1, 10, 10, 13, 16, 13, 3, 18, 1, 3, 12, 9, 9, 0] + 0) = true := bezout64

#print axioms betaGuard
#print axioms leadingSlopeCancellation
#print axioms bezout64
