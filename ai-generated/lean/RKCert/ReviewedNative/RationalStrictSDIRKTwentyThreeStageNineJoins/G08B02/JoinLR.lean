module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard008
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard011

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B02LRLL : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).drop 10).take 5).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).drop 10).take 5).take 2) pageG08B02LRLLL pageG08B02LRLLR

private theorem pageG08B02LRLRR : (rootPage (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).take 21).drop 10).take 5).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).take 21).drop 10).take 5).drop 2).drop 1) pageG08B02LRLRRL pageG08B02LRLRRR

private theorem pageG08B02LRLR : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).drop 10).take 5).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).drop 10).take 5).drop 2) pageG08B02LRLRL pageG08B02LRLRR

private theorem pageG08B02LRL : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).take 21).drop 10).take 5)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).take 21).drop 10).take 5) pageG08B02LRLL pageG08B02LRLR

private theorem pageG08B02LRRLR : (rootPage (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).take 21).drop 10).drop 5).take 3).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).take 21).drop 10).drop 5).take 3).drop 1) pageG08B02LRRLRL pageG08B02LRRLRR

private theorem pageG08B02LRRL : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).drop 10).drop 5).take 3)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).drop 10).drop 5).take 3) pageG08B02LRRLL pageG08B02LRRLR

private theorem pageG08B02LRRRR : (rootPage (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).take 21).drop 10).drop 5).drop 3).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).take 21).drop 10).drop 5).drop 3).drop 1) pageG08B02LRRRRL pageG08B02LRRRRR

private theorem pageG08B02LRRR : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).drop 10).drop 5).drop 3)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).drop 10).drop 5).drop 3) pageG08B02LRRRL pageG08B02LRRRR

private theorem pageG08B02LRR : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).take 21).drop 10).drop 5)).all paidTree = true :=
  split_right (p := paidTree) 3 (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).take 21).drop 10).drop 5) pageG08B02LRRL pageG08B02LRRR

theorem pageG08B02LR : (rootPage (treesOfOrderSucc 2) (((treesOfOrderSucc 5).take 21).drop 10)).all paidTree = true :=
  split_right (p := paidTree) 5 (treesOfOrderSucc 2) (((treesOfOrderSucc 5).take 21).drop 10) pageG08B02LRL pageG08B02LRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
