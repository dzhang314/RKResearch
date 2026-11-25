module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard008
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard011
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard012
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard013
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard014

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B00RLLLRLLR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12).take 6).drop 2) pageG08B00RLLLRLLRL pageG08B00RLLLRLLRR

private theorem pageG08B00RLLLRLL : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12).take 6) pageG08B00RLLLRLLL pageG08B00RLLLRLLR

private theorem pageG08B00RLLLRLRR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12).drop 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12).drop 6).drop 2) pageG08B00RLLLRLRRL pageG08B00RLLLRLRRR

private theorem pageG08B00RLLLRLR : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12).drop 6) pageG08B00RLLLRLRL pageG08B00RLLLRLRR

private theorem pageG08B00RLLLRL : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12) pageG08B00RLLLRLL pageG08B00RLLLRLR

private theorem pageG08B00RLLLRRLR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12).take 6).drop 2) pageG08B00RLLLRRLRL pageG08B00RLLLRRLRR

private theorem pageG08B00RLLLRRL : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12).take 6) pageG08B00RLLLRRLL pageG08B00RLLLRRLR

private theorem pageG08B00RLLLRRRL : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12).drop 6).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12).drop 6).take 4) pageG08B00RLLLRRRLL pageG08B00RLLLRRRLR

private theorem pageG08B00RLLLRRRR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12).drop 6).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12).drop 6).drop 4) pageG08B00RLLLRRRRL pageG08B00RLLLRRRRR

private theorem pageG08B00RLLLRRR : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12).drop 6) pageG08B00RLLLRRRL pageG08B00RLLLRRRR

private theorem pageG08B00RLLLRR : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).drop 12) pageG08B00RLLLRRL pageG08B00RLLLRRR

theorem pageG08B00RLLLR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26)).all paidTree = true :=
  split_right (p := paidTree) 12 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26) pageG08B00RLLLRL pageG08B00RLLLRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
