module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard008
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard011

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B05LRLL : (rootPage (((((treesOfOrderSucc 5).take 21).drop 10).take 5).take 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).take 21).drop 10).take 5).take 2) (treesOfOrderSucc 2) pageG08B05LRLLL pageG08B05LRLLR

private theorem pageG08B05LRLRR : (rootPage ((((((treesOfOrderSucc 5).take 21).drop 10).take 5).drop 2).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((((treesOfOrderSucc 5).take 21).drop 10).take 5).drop 2).drop 1) (treesOfOrderSucc 2) pageG08B05LRLRRL pageG08B05LRLRRR

private theorem pageG08B05LRLR : (rootPage (((((treesOfOrderSucc 5).take 21).drop 10).take 5).drop 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).take 21).drop 10).take 5).drop 2) (treesOfOrderSucc 2) pageG08B05LRLRL pageG08B05LRLRR

private theorem pageG08B05LRL : (rootPage ((((treesOfOrderSucc 5).take 21).drop 10).take 5) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).take 21).drop 10).take 5) (treesOfOrderSucc 2) pageG08B05LRLL pageG08B05LRLR

private theorem pageG08B05LRRLR : (rootPage ((((((treesOfOrderSucc 5).take 21).drop 10).drop 5).take 3).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((((treesOfOrderSucc 5).take 21).drop 10).drop 5).take 3).drop 1) (treesOfOrderSucc 2) pageG08B05LRRLRL pageG08B05LRRLRR

private theorem pageG08B05LRRL : (rootPage (((((treesOfOrderSucc 5).take 21).drop 10).drop 5).take 3) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).take 21).drop 10).drop 5).take 3) (treesOfOrderSucc 2) pageG08B05LRRLL pageG08B05LRRLR

private theorem pageG08B05LRRRR : (rootPage ((((((treesOfOrderSucc 5).take 21).drop 10).drop 5).drop 3).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((((treesOfOrderSucc 5).take 21).drop 10).drop 5).drop 3).drop 1) (treesOfOrderSucc 2) pageG08B05LRRRRL pageG08B05LRRRRR

private theorem pageG08B05LRRR : (rootPage (((((treesOfOrderSucc 5).take 21).drop 10).drop 5).drop 3) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).take 21).drop 10).drop 5).drop 3) (treesOfOrderSucc 2) pageG08B05LRRRL pageG08B05LRRRR

private theorem pageG08B05LRR : (rootPage ((((treesOfOrderSucc 5).take 21).drop 10).drop 5) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 3 ((((treesOfOrderSucc 5).take 21).drop 10).drop 5) (treesOfOrderSucc 2) pageG08B05LRRL pageG08B05LRRR

theorem pageG08B05LR : (rootPage (((treesOfOrderSucc 5).take 21).drop 10) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 5 (((treesOfOrderSucc 5).take 21).drop 10) (treesOfOrderSucc 2) pageG08B05LRL pageG08B05LRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
