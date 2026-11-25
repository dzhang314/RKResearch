module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard008

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B00RLLLLLLR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).take 12).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).take 12).take 6).drop 2) pageG08B00RLLLLLLRL pageG08B00RLLLLLLRR

private theorem pageG08B00RLLLLLL : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).take 12).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).take 12).take 6) pageG08B00RLLLLLLL pageG08B00RLLLLLLR

private theorem pageG08B00RLLLLLRR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).take 12).drop 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).take 12).drop 6).drop 2) pageG08B00RLLLLLRRL pageG08B00RLLLLLRRR

private theorem pageG08B00RLLLLLR : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).take 12).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).take 12).drop 6) pageG08B00RLLLLLRL pageG08B00RLLLLLRR

private theorem pageG08B00RLLLLL : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).take 12)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).take 12) pageG08B00RLLLLLL pageG08B00RLLLLLR

private theorem pageG08B00RLLLLRLR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12).take 6).drop 2) pageG08B00RLLLLRLRL pageG08B00RLLLLRLRR

private theorem pageG08B00RLLLLRL : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12).take 6) pageG08B00RLLLLRLL pageG08B00RLLLLRLR

private theorem pageG08B00RLLLLRRL : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12).drop 6).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12).drop 6).take 4) pageG08B00RLLLLRRLL pageG08B00RLLLLRRLR

private theorem pageG08B00RLLLLRRR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12).drop 6).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12).drop 6).drop 4) pageG08B00RLLLLRRRL pageG08B00RLLLLRRRR

private theorem pageG08B00RLLLLRR : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12).drop 6) pageG08B00RLLLLRRL pageG08B00RLLLLRRR

private theorem pageG08B00RLLLLR : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26).drop 12) pageG08B00RLLLLRL pageG08B00RLLLLRR

theorem pageG08B00RLLLL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26)).all paidTree = true :=
  split_right (p := paidTree) 12 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).take 26) pageG08B00RLLLLL pageG08B00RLLLLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
