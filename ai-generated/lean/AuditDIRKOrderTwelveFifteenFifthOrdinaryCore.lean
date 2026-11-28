import RKCert.ReviewedNative.DIRKOrderTwelveFifteenFifthOrdinaryCore

open RKResearch.Certified.Graded.OrderTwelveFifteen.FifthOrdinaryCore

example : (List.range 7).all (fun i => 73 % (i+2) != 0) = true := primeTrial
example : (List.range 73).filter (fun a => pStar a % 73 == 0) = roots := completeRoots
example : roots.all (fun a => a != 0 && pStarDeriv a % 73 != 0 && L₆d a % 73 != 0) = true :=
  unitGuards
example : roots.all (fun a => roots.all (fun b => (a == b) || twoClock a b % 73 != 0)) = true :=
  distinctPairs
