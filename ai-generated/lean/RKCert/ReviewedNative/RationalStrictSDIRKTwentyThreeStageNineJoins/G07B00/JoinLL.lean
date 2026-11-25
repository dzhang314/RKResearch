module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard008

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B00LLLLL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).take 4) pageG07B00LLLLLL pageG07B00LLLLLR

private theorem pageG07B00LLLLR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).drop 4) pageG07B00LLLLRL pageG07B00LLLLRR

private theorem pageG07B00LLLL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8) pageG07B00LLLLL pageG07B00LLLLR

private theorem pageG07B00LLLRL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).take 4) pageG07B00LLLRLL pageG07B00LLLRLR

private theorem pageG07B00LLLRR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8).drop 4) pageG07B00LLLRRL pageG07B00LLLRRR

private theorem pageG07B00LLLR : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).take 32).take 16).drop 8) pageG07B00LLLRL pageG07B00LLLRR

private theorem pageG07B00LLL : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).take 66).take 32).take 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).take 66).take 32).take 16) pageG07B00LLLL pageG07B00LLLR

private theorem pageG07B00LLRLL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).take 4) pageG07B00LLRLLL pageG07B00LLRLLR

private theorem pageG07B00LLRLR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8).drop 4) pageG07B00LLRLRL pageG07B00LLRLRR

private theorem pageG07B00LLRL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).take 32).drop 16).take 8) pageG07B00LLRLL pageG07B00LLRLR

private theorem pageG07B00LLRRL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).take 4) pageG07B00LLRRLL pageG07B00LLRRLR

private theorem pageG07B00LLRRR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8).drop 4) pageG07B00LLRRRL pageG07B00LLRRRR

private theorem pageG07B00LLRR : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).take 66).take 32).drop 16).drop 8) pageG07B00LLRRL pageG07B00LLRRR

private theorem pageG07B00LLR : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).take 66).take 32).drop 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).take 66).take 32).drop 16) pageG07B00LLRL pageG07B00LLRR

theorem pageG07B00LL : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 6).take 66).take 32)).all paidTree = true :=
  split_right (p := paidTree) 16 (treesOfOrderSucc 0) (((treesOfOrderSucc 6).take 66).take 32) pageG07B00LLL pageG07B00LLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
