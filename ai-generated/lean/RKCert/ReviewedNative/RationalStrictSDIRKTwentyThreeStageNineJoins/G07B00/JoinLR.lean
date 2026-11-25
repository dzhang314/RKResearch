module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard011
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard012
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard013
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard014
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard015
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard016
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard017

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B00LRLLL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).take 4) pageG07B00LRLLLL pageG07B00LRLLLR

private theorem pageG07B00LRLLR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).drop 4) pageG07B00LRLLRL pageG07B00LRLLRR

private theorem pageG07B00LRLL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8) pageG07B00LRLLL pageG07B00LRLLR

private theorem pageG07B00LRLRL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).take 4) pageG07B00LRLRLL pageG07B00LRLRLR

private theorem pageG07B00LRLRR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8).drop 4) pageG07B00LRLRRL pageG07B00LRLRRR

private theorem pageG07B00LRLR : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).drop 32).take 16).drop 8) pageG07B00LRLRL pageG07B00LRLRR

private theorem pageG07B00LRL : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).take 66).drop 32).take 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).take 66).drop 32).take 16) pageG07B00LRLL pageG07B00LRLR

private theorem pageG07B00LRRLL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).take 4) pageG07B00LRRLLL pageG07B00LRRLLR

private theorem pageG07B00LRRLR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8).drop 4) pageG07B00LRRLRL pageG07B00LRRLRR

private theorem pageG07B00LRRL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).take 8) pageG07B00LRRLL pageG07B00LRRLR

private theorem pageG07B00LRRRL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).take 4) pageG07B00LRRRLL pageG07B00LRRRLR

private theorem pageG07B00LRRRRR : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4).drop 2) pageG07B00LRRRRRL pageG07B00LRRRRRR

private theorem pageG07B00LRRRR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8).drop 4) pageG07B00LRRRRL pageG07B00LRRRRR

private theorem pageG07B00LRRR : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).drop 32).drop 16).drop 8) pageG07B00LRRRL pageG07B00LRRRR

private theorem pageG07B00LRR : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).take 66).drop 32).drop 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).take 66).drop 32).drop 16) pageG07B00LRRL pageG07B00LRRR

theorem pageG07B00LR : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 6).take 66).drop 32)).all paidTree = true :=
  split_right (p := paidTree) 16 (treesOfOrderSucc 0) (((treesOfOrderSucc 6).take 66).drop 32) pageG07B00LRL pageG07B00LRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
