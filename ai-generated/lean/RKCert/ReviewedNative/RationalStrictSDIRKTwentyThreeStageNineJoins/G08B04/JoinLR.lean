module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard008
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard009

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B04LRLL : (rootPage ((((treesOfOrderSucc 4).take 7).drop 3).take 2) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).drop 3).take 2) ((treesOfOrderSucc 3).take 2) pageG08B04LRLLL pageG08B04LRLLR

private theorem pageG08B04LRLR : (rootPage ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) ((treesOfOrderSucc 3).take 2) pageG08B04LRLRL pageG08B04LRLRR

private theorem pageG08B04LRL : (rootPage (((treesOfOrderSucc 4).take 7).drop 3) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 2 (((treesOfOrderSucc 4).take 7).drop 3) ((treesOfOrderSucc 3).take 2) pageG08B04LRLL pageG08B04LRLR

private theorem pageG08B04LRRLR : (rootPage ((((treesOfOrderSucc 4).take 7).drop 3).take 2) (((treesOfOrderSucc 3).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).drop 3).take 2) (((treesOfOrderSucc 3).drop 2).drop 1) pageG08B04LRRLRL pageG08B04LRRLRR

private theorem pageG08B04LRRL : (rootPage ((((treesOfOrderSucc 4).take 7).drop 3).take 2) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).drop 3).take 2) ((treesOfOrderSucc 3).drop 2) pageG08B04LRRLL pageG08B04LRRLR

private theorem pageG08B04LRRRR : (rootPage ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) (((treesOfOrderSucc 3).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) (((treesOfOrderSucc 3).drop 2).drop 1) pageG08B04LRRRRL pageG08B04LRRRRR

private theorem pageG08B04LRRR : (rootPage ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) ((treesOfOrderSucc 3).drop 2) pageG08B04LRRRL pageG08B04LRRRR

private theorem pageG08B04LRR : (rootPage (((treesOfOrderSucc 4).take 7).drop 3) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 2 (((treesOfOrderSucc 4).take 7).drop 3) ((treesOfOrderSucc 3).drop 2) pageG08B04LRRL pageG08B04LRRR

theorem pageG08B04LR : (rootPage (((treesOfOrderSucc 4).take 7).drop 3) (treesOfOrderSucc 3)).all paidTree = true :=
  split_right (p := paidTree) 2 (((treesOfOrderSucc 4).take 7).drop 3) (treesOfOrderSucc 3) pageG08B04LRL pageG08B04LRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
