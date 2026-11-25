module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRLRLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRLRLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RLRL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54)).all paidTree = true :=
  split_right (p := paidTree) 26 (treesOfOrderSucc 0) (((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54) pageG08B00RLRLL pageG08B00RLRLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
