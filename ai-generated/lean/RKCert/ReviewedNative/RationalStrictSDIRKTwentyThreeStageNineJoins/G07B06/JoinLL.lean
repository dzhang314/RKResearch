module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard008

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B06LLLLL : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).take 4) (treesOfOrderSucc 0) pageG07B06LLLLLL pageG07B06LLLLLR

private theorem pageG07B06LLLLR : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).drop 4) (treesOfOrderSucc 0) pageG07B06LLLLRL pageG07B06LLLLRR

private theorem pageG07B06LLLL : (rootPage (((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8) (treesOfOrderSucc 0) pageG07B06LLLLL pageG07B06LLLLR

private theorem pageG07B06LLLRL : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).take 4) (treesOfOrderSucc 0) pageG07B06LLLRLL pageG07B06LLLRLR

private theorem pageG07B06LLLRR : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).drop 4) (treesOfOrderSucc 0) pageG07B06LLLRRL pageG07B06LLLRRR

private theorem pageG07B06LLLR : (rootPage (((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8) (treesOfOrderSucc 0) pageG07B06LLLRL pageG07B06LLLRR

private theorem pageG07B06LLL : (rootPage ((((treesOfOrderSucc 6).take 66).take 32).take 16) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).take 66).take 32).take 16) (treesOfOrderSucc 0) pageG07B06LLLL pageG07B06LLLR

private theorem pageG07B06LLRLL : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).take 4) (treesOfOrderSucc 0) pageG07B06LLRLLL pageG07B06LLRLLR

private theorem pageG07B06LLRLR : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).drop 4) (treesOfOrderSucc 0) pageG07B06LLRLRL pageG07B06LLRLRR

private theorem pageG07B06LLRL : (rootPage (((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8) (treesOfOrderSucc 0) pageG07B06LLRLL pageG07B06LLRLR

private theorem pageG07B06LLRRL : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).take 4) (treesOfOrderSucc 0) pageG07B06LLRRLL pageG07B06LLRRLR

private theorem pageG07B06LLRRR : (rootPage ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 0) pageG07B06LLRRRL pageG07B06LLRRRR

private theorem pageG07B06LLRR : (rootPage (((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8) (treesOfOrderSucc 0) pageG07B06LLRRL pageG07B06LLRRR

private theorem pageG07B06LLR : (rootPage ((((treesOfOrderSucc 6).take 66).take 32).drop 16) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).take 66).take 32).drop 16) (treesOfOrderSucc 0) pageG07B06LLRL pageG07B06LLRR

theorem pageG07B06LL : (rootPage (((treesOfOrderSucc 6).take 66).take 32) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 16 (((treesOfOrderSucc 6).take 66).take 32) (treesOfOrderSucc 0) pageG07B06LLL pageG07B06LLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
