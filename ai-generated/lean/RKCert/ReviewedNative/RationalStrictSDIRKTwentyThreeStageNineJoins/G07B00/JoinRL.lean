module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard017
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard018
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard019
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard020
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard021
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard022
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard023
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard024
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard025

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B00RLLLL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).take 4) pageG07B00RLLLLL pageG07B00RLLLLR

private theorem pageG07B00RLLLR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).drop 4) pageG07B00RLLLRL pageG07B00RLLLRR

private theorem pageG07B00RLLL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8) pageG07B00RLLLL pageG07B00RLLLR

private theorem pageG07B00RLLRL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).take 4) pageG07B00RLLRLL pageG07B00RLLRLR

private theorem pageG07B00RLLRR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).drop 4) pageG07B00RLLRRL pageG07B00RLLRRR

private theorem pageG07B00RLLR : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8) pageG07B00RLLRL pageG07B00RLLRR

private theorem pageG07B00RLL : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).drop 66).take 32).take 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).drop 66).take 32).take 16) pageG07B00RLLL pageG07B00RLLR

private theorem pageG07B00RLRLL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).take 4) pageG07B00RLRLLL pageG07B00RLRLLR

private theorem pageG07B00RLRLR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).drop 4) pageG07B00RLRLRL pageG07B00RLRLRR

private theorem pageG07B00RLRL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8) pageG07B00RLRLL pageG07B00RLRLR

private theorem pageG07B00RLRRL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).take 4) pageG07B00RLRRLL pageG07B00RLRRLR

private theorem pageG07B00RLRRR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).drop 4) pageG07B00RLRRRL pageG07B00RLRRRR

private theorem pageG07B00RLRR : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8) pageG07B00RLRRL pageG07B00RLRRR

private theorem pageG07B00RLR : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).drop 66).take 32).drop 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).drop 66).take 32).drop 16) pageG07B00RLRL pageG07B00RLRR

theorem pageG07B00RL : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 6).drop 66).take 32)).all paidTree = true :=
  split_right (p := paidTree) 16 (treesOfOrderSucc 0) (((treesOfOrderSucc 6).drop 66).take 32) pageG07B00RLL pageG07B00RLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
