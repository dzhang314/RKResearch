module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard035
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard036
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard037
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard038
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard039
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard040
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard041

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B00RLRLRLLR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14).take 6).drop 2) pageG08B00RLRLRLLRL pageG08B00RLRLRLLRR

private theorem pageG08B00RLRLRLL : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14).take 6) pageG08B00RLRLRLLL pageG08B00RLRLRLLR

private theorem pageG08B00RLRLRLRL : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14).drop 6).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14).drop 6).take 4) pageG08B00RLRLRLRLL pageG08B00RLRLRLRLR

private theorem pageG08B00RLRLRLRR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14).drop 6).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14).drop 6).drop 4) pageG08B00RLRLRLRRL pageG08B00RLRLRLRRR

private theorem pageG08B00RLRLRLR : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14).drop 6) pageG08B00RLRLRLRL pageG08B00RLRLRLRR

private theorem pageG08B00RLRLRL : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).take 14) pageG08B00RLRLRLL pageG08B00RLRLRLR

private theorem pageG08B00RLRLRRLR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14).take 6).drop 2) pageG08B00RLRLRRLRL pageG08B00RLRLRRLRR

private theorem pageG08B00RLRLRRL : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14).take 6) pageG08B00RLRLRRLL pageG08B00RLRLRRLR

private theorem pageG08B00RLRLRRRL : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14).drop 6).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14).drop 6).take 4) pageG08B00RLRLRRRLL pageG08B00RLRLRRRLR

private theorem pageG08B00RLRLRRRR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14).drop 6).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14).drop 6).drop 4) pageG08B00RLRLRRRRL pageG08B00RLRLRRRRR

private theorem pageG08B00RLRLRRR : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14).drop 6) pageG08B00RLRLRRRL pageG08B00RLRLRRRR

private theorem pageG08B00RLRLRR : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26).drop 14) pageG08B00RLRLRRL pageG08B00RLRLRRR

theorem pageG08B00RLRLR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26)).all paidTree = true :=
  split_right (p := paidTree) 14 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 7).drop 1).take 214).drop 106).take 54).drop 26) pageG08B00RLRLRL pageG08B00RLRLRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
