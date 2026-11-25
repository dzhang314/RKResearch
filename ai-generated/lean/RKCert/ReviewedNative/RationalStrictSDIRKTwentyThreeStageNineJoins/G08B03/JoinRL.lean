module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard011
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard012
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard013

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B03RLLR : (rootPage ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).drop 7).take 3).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) pageG08B03RLLRL pageG08B03RLLRR

private theorem pageG08B03RLL : (rootPage ((treesOfOrderSucc 3).take 2) (((treesOfOrderSucc 4).drop 7).take 3)).all paidTree = true :=
  split_right (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) (((treesOfOrderSucc 4).drop 7).take 3) pageG08B03RLLL pageG08B03RLLR

private theorem pageG08B03RLRL : (rootPage (((treesOfOrderSucc 3).drop 2).take 1) (((treesOfOrderSucc 4).drop 7).take 3)).all paidTree = true :=
  split_right (p := paidTree) 2 (((treesOfOrderSucc 3).drop 2).take 1) (((treesOfOrderSucc 4).drop 7).take 3) pageG08B03RLRLL pageG08B03RLRLR

private theorem pageG08B03RLRRR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).drop 7).take 3).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) pageG08B03RLRRRL pageG08B03RLRRRR

private theorem pageG08B03RLRR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) (((treesOfOrderSucc 4).drop 7).take 3)).all paidTree = true :=
  split_right (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) (((treesOfOrderSucc 4).drop 7).take 3) pageG08B03RLRRL pageG08B03RLRRR

private theorem pageG08B03RLR : (rootPage ((treesOfOrderSucc 3).drop 2) (((treesOfOrderSucc 4).drop 7).take 3)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).drop 2) (((treesOfOrderSucc 4).drop 7).take 3) pageG08B03RLRL pageG08B03RLRR

theorem pageG08B03RL : (rootPage (treesOfOrderSucc 3) (((treesOfOrderSucc 4).drop 7).take 3)).all paidTree = true :=
  split_left (p := paidTree) 2 (treesOfOrderSucc 3) (((treesOfOrderSucc 4).drop 7).take 3) pageG08B03RLL pageG08B03RLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
