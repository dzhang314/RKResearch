module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard014
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard015
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard016
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard017
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard018

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B03RRLL : (rootPage ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).drop 7).drop 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) pageG08B03RRLLL pageG08B03RRLLR

private theorem pageG08B03RRLR : (rootPage ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) pageG08B03RRLRL pageG08B03RRLRR

private theorem pageG08B03RRL : (rootPage ((treesOfOrderSucc 3).take 2) (((treesOfOrderSucc 4).drop 7).drop 3)).all paidTree = true :=
  split_right (p := paidTree) 2 ((treesOfOrderSucc 3).take 2) (((treesOfOrderSucc 4).drop 7).drop 3) pageG08B03RRLL pageG08B03RRLR

private theorem pageG08B03RRRLR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).drop 7).drop 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) pageG08B03RRRLRL pageG08B03RRRLRR

private theorem pageG08B03RRRL : (rootPage ((treesOfOrderSucc 3).drop 2) ((((treesOfOrderSucc 4).drop 7).drop 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).drop 2) ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) pageG08B03RRRLL pageG08B03RRRLR

private theorem pageG08B03RRRRR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) pageG08B03RRRRRL pageG08B03RRRRRR

private theorem pageG08B03RRRR : (rootPage ((treesOfOrderSucc 3).drop 2) ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).drop 2) ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) pageG08B03RRRRL pageG08B03RRRRR

private theorem pageG08B03RRR : (rootPage ((treesOfOrderSucc 3).drop 2) (((treesOfOrderSucc 4).drop 7).drop 3)).all paidTree = true :=
  split_right (p := paidTree) 2 ((treesOfOrderSucc 3).drop 2) (((treesOfOrderSucc 4).drop 7).drop 3) pageG08B03RRRL pageG08B03RRRR

theorem pageG08B03RR : (rootPage (treesOfOrderSucc 3) (((treesOfOrderSucc 4).drop 7).drop 3)).all paidTree = true :=
  split_left (p := paidTree) 2 (treesOfOrderSucc 3) (((treesOfOrderSucc 4).drop 7).drop 3) pageG08B03RRL pageG08B03RRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
