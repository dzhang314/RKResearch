module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRLRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRLRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RRLR : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 7).drop 1).drop 214).take 106).drop 52)).all paidTree = true :=
  split_right (p := paidTree) 26 (treesOfOrderSucc 0) (((((treesOfOrderSucc 7).drop 1).drop 214).take 106).drop 52) pageG08B00RRLRL pageG08B00RRLRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
