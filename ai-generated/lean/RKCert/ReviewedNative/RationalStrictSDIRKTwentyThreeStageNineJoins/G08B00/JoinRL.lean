module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RL : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 7).drop 1).take 214)).all paidTree = true :=
  split_right (p := paidTree) 106 (treesOfOrderSucc 0) (((treesOfOrderSucc 7).drop 1).take 214) pageG08B00RLL pageG08B00RLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
