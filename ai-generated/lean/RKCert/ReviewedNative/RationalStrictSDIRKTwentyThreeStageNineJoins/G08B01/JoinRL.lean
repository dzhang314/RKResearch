module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard017
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard018
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard019
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard020
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard021
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard022
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard023
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard024
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard025

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B01RLLLL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).take 4) pageG08B01RLLLLL pageG08B01RLLLLR

private theorem pageG08B01RLLLR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8).drop 4) pageG08B01RLLLRL pageG08B01RLLLRR

private theorem pageG08B01RLLL : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).take 32).take 16).take 8) pageG08B01RLLLL pageG08B01RLLLR

private theorem pageG08B01RLLRL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).take 4) pageG08B01RLLRLL pageG08B01RLLRLR

private theorem pageG08B01RLLRR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8).drop 4) pageG08B01RLLRRL pageG08B01RLLRRR

private theorem pageG08B01RLLR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).take 32).take 16).drop 8) pageG08B01RLLRL pageG08B01RLLRR

private theorem pageG08B01RLL : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).drop 66).take 32).take 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).drop 66).take 32).take 16) pageG08B01RLLL pageG08B01RLLR

private theorem pageG08B01RLRLL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).take 4) pageG08B01RLRLLL pageG08B01RLRLLR

private theorem pageG08B01RLRLR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8).drop 4) pageG08B01RLRLRL pageG08B01RLRLRR

private theorem pageG08B01RLRL : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).take 8) pageG08B01RLRLL pageG08B01RLRLR

private theorem pageG08B01RLRRL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).take 4) pageG08B01RLRRLL pageG08B01RLRRLR

private theorem pageG08B01RLRRR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8).drop 4) pageG08B01RLRRRL pageG08B01RLRRRR

private theorem pageG08B01RLRR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).take 32).drop 16).drop 8) pageG08B01RLRRL pageG08B01RLRRR

private theorem pageG08B01RLR : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).drop 66).take 32).drop 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).drop 66).take 32).drop 16) pageG08B01RLRL pageG08B01RLRR

theorem pageG08B01RL : (rootPage (treesOfOrderSucc 1) (((treesOfOrderSucc 6).drop 66).take 32)).all paidTree = true :=
  split_right (p := paidTree) 16 (treesOfOrderSucc 1) (((treesOfOrderSucc 6).drop 66).take 32) pageG08B01RLL pageG08B01RLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
