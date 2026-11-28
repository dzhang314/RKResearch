import RKCert.ReviewedNative.DIRKOrderTwelveFifteenMidpointFourthCore
open RKResearch.Certified.Graded.OrderTwelveFifteen.MidpointFourthCore

example : (5544 : Int)-2*13860+4*12600-8*5040+16*840-32*42=0 :=
  midpointLegendreDerivative
example (q u f : Int) (h : (2*q*f+u)*(2*q*f+u)=0) : 2*q*f+u=0 :=
  clearedRepeatedRoot q u f h
