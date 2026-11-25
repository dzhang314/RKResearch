module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRLRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRLRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RLR : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 7).drop 1).take 214).drop 106)).all paidTree = true :=
  split_right (p := paidTree) 54 (treesOfOrderSucc 0) ((((treesOfOrderSucc 7).drop 1).take 214).drop 106) pageG08B00RLRL pageG08B00RLRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
