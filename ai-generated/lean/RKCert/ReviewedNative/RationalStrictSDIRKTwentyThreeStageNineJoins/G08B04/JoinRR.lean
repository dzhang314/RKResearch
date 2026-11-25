module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard014
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard015
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard016
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard017
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard018

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B04RRLL : (rootPage ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) ((treesOfOrderSucc 3).take 2) pageG08B04RRLLL pageG08B04RRLLR

private theorem pageG08B04RRLR : (rootPage ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) ((treesOfOrderSucc 3).take 2) pageG08B04RRLRL pageG08B04RRLRR

private theorem pageG08B04RRL : (rootPage (((treesOfOrderSucc 4).drop 7).drop 3) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 2 (((treesOfOrderSucc 4).drop 7).drop 3) ((treesOfOrderSucc 3).take 2) pageG08B04RRLL pageG08B04RRLR

private theorem pageG08B04RRRLR : (rootPage ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) (((treesOfOrderSucc 3).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) (((treesOfOrderSucc 3).drop 2).drop 1) pageG08B04RRRLRL pageG08B04RRRLRR

private theorem pageG08B04RRRL : (rootPage ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) ((treesOfOrderSucc 3).drop 2) pageG08B04RRRLL pageG08B04RRRLR

private theorem pageG08B04RRRRR : (rootPage ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) (((treesOfOrderSucc 3).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) (((treesOfOrderSucc 3).drop 2).drop 1) pageG08B04RRRRRL pageG08B04RRRRRR

private theorem pageG08B04RRRR : (rootPage ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) ((treesOfOrderSucc 3).drop 2) pageG08B04RRRRL pageG08B04RRRRR

private theorem pageG08B04RRR : (rootPage (((treesOfOrderSucc 4).drop 7).drop 3) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 2 (((treesOfOrderSucc 4).drop 7).drop 3) ((treesOfOrderSucc 3).drop 2) pageG08B04RRRL pageG08B04RRRR

theorem pageG08B04RR : (rootPage (((treesOfOrderSucc 4).drop 7).drop 3) (treesOfOrderSucc 3)).all paidTree = true :=
  split_right (p := paidTree) 2 (((treesOfOrderSucc 4).drop 7).drop 3) (treesOfOrderSucc 3) pageG08B04RRL pageG08B04RRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
