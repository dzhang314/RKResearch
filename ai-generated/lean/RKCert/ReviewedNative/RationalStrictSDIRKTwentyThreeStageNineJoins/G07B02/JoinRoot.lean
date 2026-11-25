module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B02.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B02.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B02.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B02.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B02.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B02.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B02.Shard007

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B02LLR : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).take 7).take 3).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).take 7).take 3).drop 1) pageG07B02LLRL pageG07B02LLRR

private theorem pageG07B02LL : (rootPage (treesOfOrderSucc 2) (((treesOfOrderSucc 4).take 7).take 3)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((treesOfOrderSucc 4).take 7).take 3) pageG07B02LLL pageG07B02LLR

private theorem pageG07B02LRL : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).take 7).drop 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).take 7).drop 3).take 2) pageG07B02LRLL pageG07B02LRLR

private theorem pageG07B02LRR : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).take 7).drop 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).take 7).drop 3).drop 2) pageG07B02LRRL pageG07B02LRRR

private theorem pageG07B02LR : (rootPage (treesOfOrderSucc 2) (((treesOfOrderSucc 4).take 7).drop 3)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 2) (((treesOfOrderSucc 4).take 7).drop 3) pageG07B02LRL pageG07B02LRR

private theorem pageG07B02L : (rootPage (treesOfOrderSucc 2) ((treesOfOrderSucc 4).take 7)).all paidTree = true :=
  split_right (p := paidTree) 3 (treesOfOrderSucc 2) ((treesOfOrderSucc 4).take 7) pageG07B02LL pageG07B02LR

private theorem pageG07B02RLR : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).drop 7).take 3).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).drop 7).take 3).drop 1) pageG07B02RLRL pageG07B02RLRR

private theorem pageG07B02RL : (rootPage (treesOfOrderSucc 2) (((treesOfOrderSucc 4).drop 7).take 3)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((treesOfOrderSucc 4).drop 7).take 3) pageG07B02RLL pageG07B02RLR

private theorem pageG07B02RRL : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).drop 7).drop 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).drop 7).drop 3).take 2) pageG07B02RRLL pageG07B02RRLR

private theorem pageG07B02RRR : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((treesOfOrderSucc 4).drop 7).drop 3).drop 2) pageG07B02RRRL pageG07B02RRRR

private theorem pageG07B02RR : (rootPage (treesOfOrderSucc 2) (((treesOfOrderSucc 4).drop 7).drop 3)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 2) (((treesOfOrderSucc 4).drop 7).drop 3) pageG07B02RRL pageG07B02RRR

private theorem pageG07B02R : (rootPage (treesOfOrderSucc 2) ((treesOfOrderSucc 4).drop 7)).all paidTree = true :=
  split_right (p := paidTree) 3 (treesOfOrderSucc 2) ((treesOfOrderSucc 4).drop 7) pageG07B02RL pageG07B02RR

theorem pageG07B02 : (rootPage (treesOfOrderSucc 2) (treesOfOrderSucc 4)).all paidTree = true :=
  split_right (p := paidTree) 7 (treesOfOrderSucc 2) (treesOfOrderSucc 4) pageG07B02L pageG07B02R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
