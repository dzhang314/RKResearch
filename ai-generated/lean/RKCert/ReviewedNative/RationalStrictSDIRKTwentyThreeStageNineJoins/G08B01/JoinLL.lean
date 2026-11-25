module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard008

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B01LLLLL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).take 4) pageG08B01LLLLLL pageG08B01LLLLLR

private theorem pageG08B01LLLLR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).drop 4) pageG08B01LLLLRL pageG08B01LLLLRR

private theorem pageG08B01LLLL : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8) pageG08B01LLLLL pageG08B01LLLLR

private theorem pageG08B01LLLRL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).take 4) pageG08B01LLLRLL pageG08B01LLLRLR

private theorem pageG08B01LLLRR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).drop 4) pageG08B01LLLRRL pageG08B01LLLRRR

private theorem pageG08B01LLLR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8) pageG08B01LLLRL pageG08B01LLLRR

private theorem pageG08B01LLL : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).take 66).take 32).take 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).take 66).take 32).take 16) pageG08B01LLLL pageG08B01LLLR

private theorem pageG08B01LLRLL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).take 4) pageG08B01LLRLLL pageG08B01LLRLLR

private theorem pageG08B01LLRLR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).drop 4) pageG08B01LLRLRL pageG08B01LLRLRR

private theorem pageG08B01LLRL : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8) pageG08B01LLRLL pageG08B01LLRLR

private theorem pageG08B01LLRRL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).take 4) pageG08B01LLRRLL pageG08B01LLRRLR

private theorem pageG08B01LLRRR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).drop 4) pageG08B01LLRRRL pageG08B01LLRRRR

private theorem pageG08B01LLRR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8) pageG08B01LLRRL pageG08B01LLRRR

private theorem pageG08B01LLR : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).take 66).take 32).drop 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).take 66).take 32).drop 16) pageG08B01LLRL pageG08B01LLRR

theorem pageG08B01LL : (rootPage (treesOfOrderSucc 1) (((treesOfOrderSucc 6).take 66).take 32)).all paidTree = true :=
  split_right (p := paidTree) 16 (treesOfOrderSucc 1) (((treesOfOrderSucc 6).take 66).take 32) pageG08B01LLL pageG08B01LLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
