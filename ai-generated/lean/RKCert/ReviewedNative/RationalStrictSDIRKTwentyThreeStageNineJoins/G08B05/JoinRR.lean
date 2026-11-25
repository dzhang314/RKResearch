module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard016
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard017
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard018
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard019
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard020
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard021

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B05RRLL : (rootPage (((((treesOfOrderSucc 5).drop 21).drop 10).take 5).take 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).drop 21).drop 10).take 5).take 2) (treesOfOrderSucc 2) pageG08B05RRLLL pageG08B05RRLLR

private theorem pageG08B05RRLRR : (rootPage ((((((treesOfOrderSucc 5).drop 21).drop 10).take 5).drop 2).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((((treesOfOrderSucc 5).drop 21).drop 10).take 5).drop 2).drop 1) (treesOfOrderSucc 2) pageG08B05RRLRRL pageG08B05RRLRRR

private theorem pageG08B05RRLR : (rootPage (((((treesOfOrderSucc 5).drop 21).drop 10).take 5).drop 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).drop 21).drop 10).take 5).drop 2) (treesOfOrderSucc 2) pageG08B05RRLRL pageG08B05RRLRR

private theorem pageG08B05RRL : (rootPage ((((treesOfOrderSucc 5).drop 21).drop 10).take 5) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).drop 21).drop 10).take 5) (treesOfOrderSucc 2) pageG08B05RRLL pageG08B05RRLR

private theorem pageG08B05RRRLR : (rootPage ((((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).take 3).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).take 3).drop 1) (treesOfOrderSucc 2) pageG08B05RRRLRL pageG08B05RRRLRR

private theorem pageG08B05RRRL : (rootPage (((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).take 3) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).take 3) (treesOfOrderSucc 2) pageG08B05RRRLL pageG08B05RRRLR

private theorem pageG08B05RRRRR : (rootPage ((((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).drop 3).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).drop 3).drop 1) (treesOfOrderSucc 2) pageG08B05RRRRRL pageG08B05RRRRRR

private theorem pageG08B05RRRR : (rootPage (((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).drop 3) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).drop 3) (treesOfOrderSucc 2) pageG08B05RRRRL pageG08B05RRRRR

private theorem pageG08B05RRR : (rootPage ((((treesOfOrderSucc 5).drop 21).drop 10).drop 5) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 3 ((((treesOfOrderSucc 5).drop 21).drop 10).drop 5) (treesOfOrderSucc 2) pageG08B05RRRL pageG08B05RRRR

theorem pageG08B05RR : (rootPage (((treesOfOrderSucc 5).drop 21).drop 10) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 5 (((treesOfOrderSucc 5).drop 21).drop 10) (treesOfOrderSucc 2) pageG08B05RRL pageG08B05RRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
