module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard008

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B06LLLLL : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).take 4) (treesOfOrderSucc 1) pageG08B06LLLLLL pageG08B06LLLLLR

private theorem pageG08B06LLLLR : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).drop 4) (treesOfOrderSucc 1) pageG08B06LLLLRL pageG08B06LLLLRR

private theorem pageG08B06LLLL : (rootPage (((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8) (treesOfOrderSucc 1) pageG08B06LLLLL pageG08B06LLLLR

private theorem pageG08B06LLLRL : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).take 4) (treesOfOrderSucc 1) pageG08B06LLLRLL pageG08B06LLLRLR

private theorem pageG08B06LLLRR : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).drop 4) (treesOfOrderSucc 1) pageG08B06LLLRRL pageG08B06LLLRRR

private theorem pageG08B06LLLR : (rootPage (((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8) (treesOfOrderSucc 1) pageG08B06LLLRL pageG08B06LLLRR

private theorem pageG08B06LLL : (rootPage ((((treesOfOrderSucc 6).take 66).take 32).take 16) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).take 66).take 32).take 16) (treesOfOrderSucc 1) pageG08B06LLLL pageG08B06LLLR

private theorem pageG08B06LLRLL : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).take 4) (treesOfOrderSucc 1) pageG08B06LLRLLL pageG08B06LLRLLR

private theorem pageG08B06LLRLR : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).drop 4) (treesOfOrderSucc 1) pageG08B06LLRLRL pageG08B06LLRLRR

private theorem pageG08B06LLRL : (rootPage (((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8) (treesOfOrderSucc 1) pageG08B06LLRLL pageG08B06LLRLR

private theorem pageG08B06LLRRL : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).take 4) (treesOfOrderSucc 1) pageG08B06LLRRLL pageG08B06LLRRLR

private theorem pageG08B06LLRRR : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 1) pageG08B06LLRRRL pageG08B06LLRRRR

private theorem pageG08B06LLRR : (rootPage (((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8) (treesOfOrderSucc 1) pageG08B06LLRRL pageG08B06LLRRR

private theorem pageG08B06LLR : (rootPage ((((treesOfOrderSucc 6).take 66).take 32).drop 16) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).take 66).take 32).drop 16) (treesOfOrderSucc 1) pageG08B06LLRL pageG08B06LLRR

theorem pageG08B06LL : (rootPage (((treesOfOrderSucc 6).take 66).take 32) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 16 (((treesOfOrderSucc 6).take 66).take 32) (treesOfOrderSucc 1) pageG08B06LLL pageG08B06LLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
