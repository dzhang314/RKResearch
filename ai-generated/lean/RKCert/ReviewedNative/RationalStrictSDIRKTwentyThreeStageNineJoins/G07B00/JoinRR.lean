module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard025
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard026
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard027
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard028
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard029
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard030
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard031
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard032
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B00.Shard033

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B00RRLLL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).take 4) pageG07B00RRLLLL pageG07B00RRLLLR

private theorem pageG07B00RRLLR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).drop 4) pageG07B00RRLLRL pageG07B00RRLLRR

private theorem pageG07B00RRLL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8) pageG07B00RRLLL pageG07B00RRLLR

private theorem pageG07B00RRLRL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).take 4) pageG07B00RRLRLL pageG07B00RRLRLR

private theorem pageG07B00RRLRR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).drop 4) pageG07B00RRLRRL pageG07B00RRLRRR

private theorem pageG07B00RRLR : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8) pageG07B00RRLRL pageG07B00RRLRR

private theorem pageG07B00RRL : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).drop 66).drop 32).take 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).drop 66).drop 32).take 16) pageG07B00RRLL pageG07B00RRLR

private theorem pageG07B00RRRLL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).take 4) pageG07B00RRRLLL pageG07B00RRRLLR

private theorem pageG07B00RRRLR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).drop 4) pageG07B00RRRLRL pageG07B00RRRLRR

private theorem pageG07B00RRRL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8) pageG07B00RRRLL pageG07B00RRRLR

private theorem pageG07B00RRRRL : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).take 4) pageG07B00RRRRLL pageG07B00RRRRLR

private theorem pageG07B00RRRRRR : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) (((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4).drop 2) pageG07B00RRRRRRL pageG07B00RRRRRRR

private theorem pageG07B00RRRRR : (rootPage (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 0) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4) pageG07B00RRRRRL pageG07B00RRRRRR

private theorem pageG07B00RRRR : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8) pageG07B00RRRRL pageG07B00RRRRR

private theorem pageG07B00RRR : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).drop 66).drop 32).drop 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 0) ((((treesOfOrderSucc 6).drop 66).drop 32).drop 16) pageG07B00RRRL pageG07B00RRRR

theorem pageG07B00RR : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 6).drop 66).drop 32)).all paidTree = true :=
  split_right (p := paidTree) 16 (treesOfOrderSucc 0) (((treesOfOrderSucc 6).drop 66).drop 32) pageG07B00RRL pageG07B00RRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
