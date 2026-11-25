module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard017
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard018
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard019
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard020
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard021
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard022
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard023
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard024
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard025

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B06RLLLL : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).take 4) (treesOfOrderSucc 0) pageG07B06RLLLLL pageG07B06RLLLLR

private theorem pageG07B06RLLLR : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).drop 4) (treesOfOrderSucc 0) pageG07B06RLLLRL pageG07B06RLLLRR

private theorem pageG07B06RLLL : (rootPage (((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8) (treesOfOrderSucc 0) pageG07B06RLLLL pageG07B06RLLLR

private theorem pageG07B06RLLRL : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).take 4) (treesOfOrderSucc 0) pageG07B06RLLRLL pageG07B06RLLRLR

private theorem pageG07B06RLLRR : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).drop 4) (treesOfOrderSucc 0) pageG07B06RLLRRL pageG07B06RLLRRR

private theorem pageG07B06RLLR : (rootPage (((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8) (treesOfOrderSucc 0) pageG07B06RLLRL pageG07B06RLLRR

private theorem pageG07B06RLL : (rootPage ((((treesOfOrderSucc 6).drop 66).take 32).take 16) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).drop 66).take 32).take 16) (treesOfOrderSucc 0) pageG07B06RLLL pageG07B06RLLR

private theorem pageG07B06RLRLL : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).take 4) (treesOfOrderSucc 0) pageG07B06RLRLLL pageG07B06RLRLLR

private theorem pageG07B06RLRLR : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).drop 4) (treesOfOrderSucc 0) pageG07B06RLRLRL pageG07B06RLRLRR

private theorem pageG07B06RLRL : (rootPage (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8) (treesOfOrderSucc 0) pageG07B06RLRLL pageG07B06RLRLR

private theorem pageG07B06RLRRL : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).take 4) (treesOfOrderSucc 0) pageG07B06RLRRLL pageG07B06RLRRLR

private theorem pageG07B06RLRRR : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 0) pageG07B06RLRRRL pageG07B06RLRRRR

private theorem pageG07B06RLRR : (rootPage (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8) (treesOfOrderSucc 0) pageG07B06RLRRL pageG07B06RLRRR

private theorem pageG07B06RLR : (rootPage ((((treesOfOrderSucc 6).drop 66).take 32).drop 16) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).drop 66).take 32).drop 16) (treesOfOrderSucc 0) pageG07B06RLRL pageG07B06RLRR

theorem pageG07B06RL : (rootPage (((treesOfOrderSucc 6).drop 66).take 32) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 16 (((treesOfOrderSucc 6).drop 66).take 32) (treesOfOrderSucc 0) pageG07B06RLL pageG07B06RLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
