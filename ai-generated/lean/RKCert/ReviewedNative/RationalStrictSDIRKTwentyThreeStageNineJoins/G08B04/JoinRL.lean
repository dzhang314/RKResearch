module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard011
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard012
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard013

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B04RLLR : (rootPage ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) ((treesOfOrderSucc 3).take 2) pageG08B04RLLRL pageG08B04RLLRR

private theorem pageG08B04RLL : (rootPage (((treesOfOrderSucc 4).drop 7).take 3) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 4).drop 7).take 3) ((treesOfOrderSucc 3).take 2) pageG08B04RLLL pageG08B04RLLR

private theorem pageG08B04RLRL : (rootPage ((((treesOfOrderSucc 4).drop 7).take 3).take 1) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 ((((treesOfOrderSucc 4).drop 7).take 3).take 1) ((treesOfOrderSucc 3).drop 2) pageG08B04RLRLL pageG08B04RLRLR

private theorem pageG08B04RLRRR : (rootPage ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) (((treesOfOrderSucc 3).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) (((treesOfOrderSucc 3).drop 2).drop 1) pageG08B04RLRRRL pageG08B04RLRRRR

private theorem pageG08B04RLRR : (rootPage ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) ((treesOfOrderSucc 3).drop 2) pageG08B04RLRRL pageG08B04RLRRR

private theorem pageG08B04RLR : (rootPage (((treesOfOrderSucc 4).drop 7).take 3) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 4).drop 7).take 3) ((treesOfOrderSucc 3).drop 2) pageG08B04RLRL pageG08B04RLRR

theorem pageG08B04RL : (rootPage (((treesOfOrderSucc 4).drop 7).take 3) (treesOfOrderSucc 3)).all paidTree = true :=
  split_right (p := paidTree) 2 (((treesOfOrderSucc 4).drop 7).take 3) (treesOfOrderSucc 3) pageG08B04RLL pageG08B04RLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
