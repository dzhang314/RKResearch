module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard011
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard012
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard013
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard014
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard015
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard016
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard017

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B01LRLLL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).take 4) pageG08B01LRLLLL pageG08B01LRLLLR

private theorem pageG08B01LRLLR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).drop 4) pageG08B01LRLLRL pageG08B01LRLLRR

private theorem pageG08B01LRLL : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8) pageG08B01LRLLL pageG08B01LRLLR

private theorem pageG08B01LRLRL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).take 4) pageG08B01LRLRLL pageG08B01LRLRLR

private theorem pageG08B01LRLRR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).drop 4) pageG08B01LRLRRL pageG08B01LRLRRR

private theorem pageG08B01LRLR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8) pageG08B01LRLRL pageG08B01LRLRR

private theorem pageG08B01LRL : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).take 66).drop 32).take 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).take 66).drop 32).take 16) pageG08B01LRLL pageG08B01LRLR

private theorem pageG08B01LRRLL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).take 4) pageG08B01LRRLLL pageG08B01LRRLLR

private theorem pageG08B01LRRLR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).drop 4) pageG08B01LRRLRL pageG08B01LRRLRR

private theorem pageG08B01LRRL : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8) pageG08B01LRRLL pageG08B01LRRLR

private theorem pageG08B01LRRRL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).take 4) pageG08B01LRRRLL pageG08B01LRRRLR

private theorem pageG08B01LRRRRR : (rootPage (treesOfOrderSucc 1) (((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) (((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4).drop 2) pageG08B01LRRRRRL pageG08B01LRRRRRR

private theorem pageG08B01LRRRR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4) pageG08B01LRRRRL pageG08B01LRRRRR

private theorem pageG08B01LRRR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8) pageG08B01LRRRL pageG08B01LRRRR

private theorem pageG08B01LRR : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).take 66).drop 32).drop 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).take 66).drop 32).drop 16) pageG08B01LRRL pageG08B01LRRR

theorem pageG08B01LR : (rootPage (treesOfOrderSucc 1) (((treesOfOrderSucc 6).take 66).drop 32)).all paidTree = true :=
  split_right (p := paidTree) 16 (treesOfOrderSucc 1) (((treesOfOrderSucc 6).take 66).drop 32) pageG08B01LRL pageG08B01LRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
