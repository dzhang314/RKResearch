module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard102
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard103
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard104
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard105
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard106
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard107
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard108

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B00RRRRRLLR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14).take 6).drop 2) pageG08B00RRRRRLLRL pageG08B00RRRRRLLRR

private theorem pageG08B00RRRRRLL : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14).take 6) pageG08B00RRRRRLLL pageG08B00RRRRRLLR

private theorem pageG08B00RRRRRLRL : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14).drop 6).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14).drop 6).take 4) pageG08B00RRRRRLRLL pageG08B00RRRRRLRLR

private theorem pageG08B00RRRRRLRR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14).drop 6).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14).drop 6).drop 4) pageG08B00RRRRRLRRL pageG08B00RRRRRLRRR

private theorem pageG08B00RRRRRLR : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14).drop 6) pageG08B00RRRRRLRL pageG08B00RRRRRLRR

private theorem pageG08B00RRRRRL : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).take 14) pageG08B00RRRRRLL pageG08B00RRRRRLR

private theorem pageG08B00RRRRRRLR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14).take 6).drop 2) pageG08B00RRRRRRLRL pageG08B00RRRRRRLRR

private theorem pageG08B00RRRRRRL : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14).take 6) pageG08B00RRRRRRLL pageG08B00RRRRRRLR

private theorem pageG08B00RRRRRRRL : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6).take 4) pageG08B00RRRRRRRLL pageG08B00RRRRRRRLR

private theorem pageG08B00RRRRRRRR : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6).drop 4) pageG08B00RRRRRRRRL pageG08B00RRRRRRRRR

private theorem pageG08B00RRRRRRR : (rootPage (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) ((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6) pageG08B00RRRRRRRL pageG08B00RRRRRRRR

private theorem pageG08B00RRRRRR : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26).drop 14) pageG08B00RRRRRRL pageG08B00RRRRRRR

theorem pageG08B00RRRRR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26)).all paidTree = true :=
  split_right (p := paidTree) 14 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).drop 26) pageG08B00RRRRRL pageG08B00RRRRRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
