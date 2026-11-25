module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRLLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRLLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RRLL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 7).drop 1).drop 214).take 106).take 52)).all paidTree = true :=
  split_right (p := paidTree) 26 (treesOfOrderSucc 0) (((((treesOfOrderSucc 7).drop 1).drop 214).take 106).take 52) pageG08B00RRLLL pageG08B00RRLLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
