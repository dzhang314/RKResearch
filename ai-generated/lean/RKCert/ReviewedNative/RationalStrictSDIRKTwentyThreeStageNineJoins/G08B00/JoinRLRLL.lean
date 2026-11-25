module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard028
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard029
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard030
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard031
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard032
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard033
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard034

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B00RLRLLLLR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).take 12).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).take 12).take 6).drop 2) pageG08B00RLRLLLLRL pageG08B00RLRLLLLRR

private theorem pageG08B00RLRLLLL : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).take 12).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).take 12).take 6) pageG08B00RLRLLLLL pageG08B00RLRLLLLR

private theorem pageG08B00RLRLLLRR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).take 12).drop 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).take 12).drop 6).drop 2) pageG08B00RLRLLLRRL pageG08B00RLRLLLRRR

private theorem pageG08B00RLRLLLR : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).take 12).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).take 12).drop 6) pageG08B00RLRLLLRL pageG08B00RLRLLLRR

private theorem pageG08B00RLRLLL : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).take 12)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).take 12) pageG08B00RLRLLLL pageG08B00RLRLLLR

private theorem pageG08B00RLRLLRLR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12).take 6).drop 2) pageG08B00RLRLLRLRL pageG08B00RLRLLRLRR

private theorem pageG08B00RLRLLRL : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12).take 6) pageG08B00RLRLLRLL pageG08B00RLRLLRLR

private theorem pageG08B00RLRLLRRL : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12).drop 6).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12).drop 6).take 4) pageG08B00RLRLLRRLL pageG08B00RLRLLRRLR

private theorem pageG08B00RLRLLRRR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12).drop 6).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12).drop 6).drop 4) pageG08B00RLRLLRRRL pageG08B00RLRLLRRRR

private theorem pageG08B00RLRLLRR : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12).drop 6) pageG08B00RLRLLRRL pageG08B00RLRLLRRR

private theorem pageG08B00RLRLLR : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26).drop 12) pageG08B00RLRLLRL pageG08B00RLRLLRR

theorem pageG08B00RLRLL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26)).all paidTree = true :=
  split_right (p := paidTree) 12 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).take 26) pageG08B00RLRLLL pageG08B00RLRLLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
