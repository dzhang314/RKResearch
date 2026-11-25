module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard017
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard018
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard019
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard020
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard021
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard022
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard023
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard024
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard025

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B06RLLLL : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).take 4) (treesOfOrderSucc 1) pageG08B06RLLLLL pageG08B06RLLLLR

private theorem pageG08B06RLLLR : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).drop 4) (treesOfOrderSucc 1) pageG08B06RLLLRL pageG08B06RLLLRR

private theorem pageG08B06RLLL : (rootPage (((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8) (treesOfOrderSucc 1) pageG08B06RLLLL pageG08B06RLLLR

private theorem pageG08B06RLLRL : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).take 4) (treesOfOrderSucc 1) pageG08B06RLLRLL pageG08B06RLLRLR

private theorem pageG08B06RLLRR : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).drop 4) (treesOfOrderSucc 1) pageG08B06RLLRRL pageG08B06RLLRRR

private theorem pageG08B06RLLR : (rootPage (((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8) (treesOfOrderSucc 1) pageG08B06RLLRL pageG08B06RLLRR

private theorem pageG08B06RLL : (rootPage ((((treesOfOrderSucc 6).drop 66).take 32).take 16) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).drop 66).take 32).take 16) (treesOfOrderSucc 1) pageG08B06RLLL pageG08B06RLLR

private theorem pageG08B06RLRLL : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).take 4) (treesOfOrderSucc 1) pageG08B06RLRLLL pageG08B06RLRLLR

private theorem pageG08B06RLRLR : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).drop 4) (treesOfOrderSucc 1) pageG08B06RLRLRL pageG08B06RLRLRR

private theorem pageG08B06RLRL : (rootPage (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8) (treesOfOrderSucc 1) pageG08B06RLRLL pageG08B06RLRLR

private theorem pageG08B06RLRRL : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).take 4) (treesOfOrderSucc 1) pageG08B06RLRRLL pageG08B06RLRRLR

private theorem pageG08B06RLRRR : (rootPage ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 1) pageG08B06RLRRRL pageG08B06RLRRRR

private theorem pageG08B06RLRR : (rootPage (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8) (treesOfOrderSucc 1) pageG08B06RLRRL pageG08B06RLRRR

private theorem pageG08B06RLR : (rootPage ((((treesOfOrderSucc 6).drop 66).take 32).drop 16) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).drop 66).take 32).drop 16) (treesOfOrderSucc 1) pageG08B06RLRL pageG08B06RLRR

theorem pageG08B06RL : (rootPage (((treesOfOrderSucc 6).drop 66).take 32) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 16 (((treesOfOrderSucc 6).drop 66).take 32) (treesOfOrderSucc 1) pageG08B06RLL pageG08B06RLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
