module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard011
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard012
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard013
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard014
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard015
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard016
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard017

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B06LRLLL : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).take 4) (treesOfOrderSucc 0) pageG07B06LRLLLL pageG07B06LRLLLR

private theorem pageG07B06LRLLR : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).drop 4) (treesOfOrderSucc 0) pageG07B06LRLLRL pageG07B06LRLLRR

private theorem pageG07B06LRLL : (rootPage (((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8) (treesOfOrderSucc 0) pageG07B06LRLLL pageG07B06LRLLR

private theorem pageG07B06LRLRL : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).take 4) (treesOfOrderSucc 0) pageG07B06LRLRLL pageG07B06LRLRLR

private theorem pageG07B06LRLRR : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).drop 4) (treesOfOrderSucc 0) pageG07B06LRLRRL pageG07B06LRLRRR

private theorem pageG07B06LRLR : (rootPage (((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8) (treesOfOrderSucc 0) pageG07B06LRLRL pageG07B06LRLRR

private theorem pageG07B06LRL : (rootPage ((((treesOfOrderSucc 6).take 66).drop 32).take 16) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).take 66).drop 32).take 16) (treesOfOrderSucc 0) pageG07B06LRLL pageG07B06LRLR

private theorem pageG07B06LRRLL : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).take 4) (treesOfOrderSucc 0) pageG07B06LRRLLL pageG07B06LRRLLR

private theorem pageG07B06LRRLR : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).drop 4) (treesOfOrderSucc 0) pageG07B06LRRLRL pageG07B06LRRLRR

private theorem pageG07B06LRRL : (rootPage (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8) (treesOfOrderSucc 0) pageG07B06LRRLL pageG07B06LRRLR

private theorem pageG07B06LRRRL : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).take 4) (treesOfOrderSucc 0) pageG07B06LRRRLL pageG07B06LRRRLR

private theorem pageG07B06LRRRRR : (rootPage (((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4).drop 2) (treesOfOrderSucc 0) pageG07B06LRRRRRL pageG07B06LRRRRRR

private theorem pageG07B06LRRRR : (rootPage ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 0) pageG07B06LRRRRL pageG07B06LRRRRR

private theorem pageG07B06LRRR : (rootPage (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8) (treesOfOrderSucc 0) pageG07B06LRRRL pageG07B06LRRRR

private theorem pageG07B06LRR : (rootPage ((((treesOfOrderSucc 6).take 66).drop 32).drop 16) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).take 66).drop 32).drop 16) (treesOfOrderSucc 0) pageG07B06LRRL pageG07B06LRRR

theorem pageG07B06LR : (rootPage (((treesOfOrderSucc 6).take 66).drop 32) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 16 (((treesOfOrderSucc 6).take 66).drop 32) (treesOfOrderSucc 0) pageG07B06LRL pageG07B06LRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
