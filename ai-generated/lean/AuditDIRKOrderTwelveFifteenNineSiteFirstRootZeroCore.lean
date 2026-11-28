import RKCert.ReviewedNative.DIRKOrderTwelveFifteenNineSiteFirstRootZeroCore
open RKResearch.Certified.Graded.OrderTwelveFifteen.NineSiteFirstRootZeroCore

example : (List.range 9).all (fun i => 113 % (i+2) != 0) = true := primeTrial
example : (List.range 113).filter (fun a => l6d (Int.ofNat a) % 113 == 0) =
    baseResiduals := completeBase
example : baseResiduals.all (fun a =>
    a != 0 && momentPivot a % 113 != 0 && ((hQuartic a)[4]?).getD 0 % 113 != 0) = true :=
  leadingGuards
example : hFactors.all test = true := hFactorProducts
