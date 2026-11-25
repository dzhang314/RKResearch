module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard025
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard026
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard027
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard028
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard029
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard030
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard031
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard032
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B01.Shard033

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B01RRLLL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).take 4) pageG08B01RRLLLL pageG08B01RRLLLR

private theorem pageG08B01RRLLR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).drop 4) pageG08B01RRLLRL pageG08B01RRLLRR

private theorem pageG08B01RRLL : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8) pageG08B01RRLLL pageG08B01RRLLR

private theorem pageG08B01RRLRL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).take 4) pageG08B01RRLRLL pageG08B01RRLRLR

private theorem pageG08B01RRLRR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).drop 4) pageG08B01RRLRRL pageG08B01RRLRRR

private theorem pageG08B01RRLR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8) pageG08B01RRLRL pageG08B01RRLRR

private theorem pageG08B01RRL : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).drop 66).drop 32).take 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).drop 66).drop 32).take 16) pageG08B01RRLL pageG08B01RRLR

private theorem pageG08B01RRRLL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).take 4) pageG08B01RRRLLL pageG08B01RRRLLR

private theorem pageG08B01RRRLR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).drop 4) pageG08B01RRRLRL pageG08B01RRRLRR

private theorem pageG08B01RRRL : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8) pageG08B01RRRLL pageG08B01RRRLR

private theorem pageG08B01RRRRL : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).take 4) pageG08B01RRRRLL pageG08B01RRRRLR

private theorem pageG08B01RRRRRR : (rootPage (treesOfOrderSucc 1) (((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) (((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4).drop 2) pageG08B01RRRRRRL pageG08B01RRRRRRR

private theorem pageG08B01RRRRR : (rootPage (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4) pageG08B01RRRRRL pageG08B01RRRRRR

private theorem pageG08B01RRRR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8) pageG08B01RRRRL pageG08B01RRRRR

private theorem pageG08B01RRR : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).drop 66).drop 32).drop 16)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 1) ((((treesOfOrderSucc 6).drop 66).drop 32).drop 16) pageG08B01RRRL pageG08B01RRRR

theorem pageG08B01RR : (rootPage (treesOfOrderSucc 1) (((treesOfOrderSucc 6).drop 66).drop 32)).all paidTree = true :=
  split_right (p := paidTree) 16 (treesOfOrderSucc 1) (((treesOfOrderSucc 6).drop 66).drop 32) pageG08B01RRL pageG08B01RRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
