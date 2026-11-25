module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard011
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard012
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard013
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard014
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard015
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard016
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard017

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B06LRLLL : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).take 4) (treesOfOrderSucc 1) pageG08B06LRLLLL pageG08B06LRLLLR

private theorem pageG08B06LRLLR : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).drop 4) (treesOfOrderSucc 1) pageG08B06LRLLRL pageG08B06LRLLRR

private theorem pageG08B06LRLL : (rootPage (((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8) (treesOfOrderSucc 1) pageG08B06LRLLL pageG08B06LRLLR

private theorem pageG08B06LRLRL : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).take 4) (treesOfOrderSucc 1) pageG08B06LRLRLL pageG08B06LRLRLR

private theorem pageG08B06LRLRR : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).drop 4) (treesOfOrderSucc 1) pageG08B06LRLRRL pageG08B06LRLRRR

private theorem pageG08B06LRLR : (rootPage (((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8) (treesOfOrderSucc 1) pageG08B06LRLRL pageG08B06LRLRR

private theorem pageG08B06LRL : (rootPage ((((treesOfOrderSucc 6).take 66).drop 32).take 16) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).take 66).drop 32).take 16) (treesOfOrderSucc 1) pageG08B06LRLL pageG08B06LRLR

private theorem pageG08B06LRRLL : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).take 4) (treesOfOrderSucc 1) pageG08B06LRRLLL pageG08B06LRRLLR

private theorem pageG08B06LRRLR : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).drop 4) (treesOfOrderSucc 1) pageG08B06LRRLRL pageG08B06LRRLRR

private theorem pageG08B06LRRL : (rootPage (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8) (treesOfOrderSucc 1) pageG08B06LRRLL pageG08B06LRRLR

private theorem pageG08B06LRRRL : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).take 4) (treesOfOrderSucc 1) pageG08B06LRRRLL pageG08B06LRRRLR

private theorem pageG08B06LRRRRR : (rootPage (((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4).drop 2) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4).drop 2) (treesOfOrderSucc 1) pageG08B06LRRRRRL pageG08B06LRRRRRR

private theorem pageG08B06LRRRR : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 1) pageG08B06LRRRRL pageG08B06LRRRRR

private theorem pageG08B06LRRR : (rootPage (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8) (treesOfOrderSucc 1) pageG08B06LRRRL pageG08B06LRRRR

private theorem pageG08B06LRR : (rootPage ((((treesOfOrderSucc 6).take 66).drop 32).drop 16) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).take 66).drop 32).drop 16) (treesOfOrderSucc 1) pageG08B06LRRL pageG08B06LRRR

theorem pageG08B06LR : (rootPage (((treesOfOrderSucc 6).take 66).drop 32) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 16 (((treesOfOrderSucc 6).take 66).drop 32) (treesOfOrderSucc 1) pageG08B06LRL pageG08B06LRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
