module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard008
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard009

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B03LRLL : (rootPage ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).take 7).drop 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).take 7).drop 3).take 2) pageG08B03LRLLL pageG08B03LRLLR

private theorem pageG08B03LRLR : (rootPage ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).take 7).drop 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) pageG08B03LRLRL pageG08B03LRLRR

private theorem pageG08B03LRL : (rootPage ((treesOfOrderSucc 3).take 2) (((treesOfOrderSucc 4).take 7).drop 3)).all paidTree = true :=
  split_right (p := paidTree) 2 ((treesOfOrderSucc 3).take 2) (((treesOfOrderSucc 4).take 7).drop 3) pageG08B03LRLL pageG08B03LRLR

private theorem pageG08B03LRRLR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).take 7).drop 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).take 7).drop 3).take 2) pageG08B03LRRLRL pageG08B03LRRLRR

private theorem pageG08B03LRRL : (rootPage ((treesOfOrderSucc 3).drop 2) ((((treesOfOrderSucc 4).take 7).drop 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).drop 2) ((((treesOfOrderSucc 4).take 7).drop 3).take 2) pageG08B03LRRLL pageG08B03LRRLR

private theorem pageG08B03LRRRR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).take 7).drop 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) pageG08B03LRRRRL pageG08B03LRRRRR

private theorem pageG08B03LRRR : (rootPage ((treesOfOrderSucc 3).drop 2) ((((treesOfOrderSucc 4).take 7).drop 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).drop 2) ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) pageG08B03LRRRL pageG08B03LRRRR

private theorem pageG08B03LRR : (rootPage ((treesOfOrderSucc 3).drop 2) (((treesOfOrderSucc 4).take 7).drop 3)).all paidTree = true :=
  split_right (p := paidTree) 2 ((treesOfOrderSucc 3).drop 2) (((treesOfOrderSucc 4).take 7).drop 3) pageG08B03LRRL pageG08B03LRRR

theorem pageG08B03LR : (rootPage (treesOfOrderSucc 3) (((treesOfOrderSucc 4).take 7).drop 3)).all paidTree = true :=
  split_left (p := paidTree) 2 (treesOfOrderSucc 3) (((treesOfOrderSucc 4).take 7).drop 3) pageG08B03LRL pageG08B03LRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
