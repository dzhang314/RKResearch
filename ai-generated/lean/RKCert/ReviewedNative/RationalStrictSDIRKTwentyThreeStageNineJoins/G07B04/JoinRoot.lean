module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B04.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B04.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B04.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B04.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B04.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B04.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B04.Shard007

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B04LLR : (rootPage ((((treesOfOrderSucc 4).take 7).take 3).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).take 3).drop 1) (treesOfOrderSucc 2) pageG07B04LLRL pageG07B04LLRR

private theorem pageG07B04LL : (rootPage (((treesOfOrderSucc 4).take 7).take 3) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 4).take 7).take 3) (treesOfOrderSucc 2) pageG07B04LLL pageG07B04LLR

private theorem pageG07B04LRL : (rootPage ((((treesOfOrderSucc 4).take 7).drop 3).take 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).drop 3).take 2) (treesOfOrderSucc 2) pageG07B04LRLL pageG07B04LRLR

private theorem pageG07B04LRR : (rootPage ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) (treesOfOrderSucc 2) pageG07B04LRRL pageG07B04LRRR

private theorem pageG07B04LR : (rootPage (((treesOfOrderSucc 4).take 7).drop 3) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 2 (((treesOfOrderSucc 4).take 7).drop 3) (treesOfOrderSucc 2) pageG07B04LRL pageG07B04LRR

private theorem pageG07B04L : (rootPage ((treesOfOrderSucc 4).take 7) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 3 ((treesOfOrderSucc 4).take 7) (treesOfOrderSucc 2) pageG07B04LL pageG07B04LR

private theorem pageG07B04RLR : (rootPage ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) (treesOfOrderSucc 2) pageG07B04RLRL pageG07B04RLRR

private theorem pageG07B04RL : (rootPage (((treesOfOrderSucc 4).drop 7).take 3) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 4).drop 7).take 3) (treesOfOrderSucc 2) pageG07B04RLL pageG07B04RLR

private theorem pageG07B04RRL : (rootPage ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) (treesOfOrderSucc 2) pageG07B04RRLL pageG07B04RRLR

private theorem pageG07B04RRR : (rootPage ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) (treesOfOrderSucc 2) pageG07B04RRRL pageG07B04RRRR

private theorem pageG07B04RR : (rootPage (((treesOfOrderSucc 4).drop 7).drop 3) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 2 (((treesOfOrderSucc 4).drop 7).drop 3) (treesOfOrderSucc 2) pageG07B04RRL pageG07B04RRR

private theorem pageG07B04R : (rootPage ((treesOfOrderSucc 4).drop 7) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 3 ((treesOfOrderSucc 4).drop 7) (treesOfOrderSucc 2) pageG07B04RL pageG07B04RR

theorem pageG07B04 : (rootPage (treesOfOrderSucc 4) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 7 (treesOfOrderSucc 4) (treesOfOrderSucc 2) pageG07B04L pageG07B04R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
