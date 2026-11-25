module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard016
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard017
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard018
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard019
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard020
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard021

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B02RRLL : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).drop 10).take 5).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).drop 10).take 5).take 2) pageG08B02RRLLL pageG08B02RRLLR

private theorem pageG08B02RRLRR : (rootPage (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).drop 21).drop 10).take 5).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).drop 21).drop 10).take 5).drop 2).drop 1) pageG08B02RRLRRL pageG08B02RRLRRR

private theorem pageG08B02RRLR : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).drop 10).take 5).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).drop 10).take 5).drop 2) pageG08B02RRLRL pageG08B02RRLRR

private theorem pageG08B02RRL : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).drop 21).drop 10).take 5)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).drop 21).drop 10).take 5) pageG08B02RRLL pageG08B02RRLR

private theorem pageG08B02RRRLR : (rootPage (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).take 3).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).take 3).drop 1) pageG08B02RRRLRL pageG08B02RRRLRR

private theorem pageG08B02RRRL : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).take 3)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).take 3) pageG08B02RRRLL pageG08B02RRRLR

private theorem pageG08B02RRRRR : (rootPage (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).drop 3).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).drop 3).drop 1) pageG08B02RRRRRL pageG08B02RRRRRR

private theorem pageG08B02RRRR : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).drop 3)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).drop 10).drop 5).drop 3) pageG08B02RRRRL pageG08B02RRRRR

private theorem pageG08B02RRR : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).drop 21).drop 10).drop 5)).all paidTree = true :=
  split_right (p := paidTree) 3 (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).drop 21).drop 10).drop 5) pageG08B02RRRL pageG08B02RRRR

theorem pageG08B02RR : (rootPage (treesOfOrderSucc 2) (((treesOfOrderSucc 5).drop 21).drop 10)).all paidTree = true :=
  split_right (p := paidTree) 5 (treesOfOrderSucc 2) (((treesOfOrderSucc 5).drop 21).drop 10) pageG08B02RRL pageG08B02RRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
