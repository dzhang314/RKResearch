module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B03.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B03.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B03.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B03.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B03.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B03.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B03.Shard007

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B03LL : (rootPage ((treesOfOrderSucc 3).take 2) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) ((treesOfOrderSucc 3).take 2) pageG07B03LLL pageG07B03LLR

private theorem pageG07B03LRR : (rootPage ((treesOfOrderSucc 3).take 2) (((treesOfOrderSucc 3).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) (((treesOfOrderSucc 3).drop 2).drop 1) pageG07B03LRRL pageG07B03LRRR

private theorem pageG07B03LR : (rootPage ((treesOfOrderSucc 3).take 2) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) ((treesOfOrderSucc 3).drop 2) pageG07B03LRL pageG07B03LRR

private theorem pageG07B03L : (rootPage ((treesOfOrderSucc 3).take 2) (treesOfOrderSucc 3)).all paidTree = true :=
  split_right (p := paidTree) 2 ((treesOfOrderSucc 3).take 2) (treesOfOrderSucc 3) pageG07B03LL pageG07B03LR

private theorem pageG07B03RLR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) ((treesOfOrderSucc 3).take 2) pageG07B03RLRL pageG07B03RLRR

private theorem pageG07B03RL : (rootPage ((treesOfOrderSucc 3).drop 2) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).drop 2) ((treesOfOrderSucc 3).take 2) pageG07B03RLL pageG07B03RLR

private theorem pageG07B03RRL : (rootPage (((treesOfOrderSucc 3).drop 2).take 1) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (((treesOfOrderSucc 3).drop 2).take 1) ((treesOfOrderSucc 3).drop 2) pageG07B03RRLL pageG07B03RRLR

private theorem pageG07B03RRRR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) (((treesOfOrderSucc 3).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) (((treesOfOrderSucc 3).drop 2).drop 1) pageG07B03RRRRL pageG07B03RRRRR

private theorem pageG07B03RRR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) ((treesOfOrderSucc 3).drop 2) pageG07B03RRRL pageG07B03RRRR

private theorem pageG07B03RR : (rootPage ((treesOfOrderSucc 3).drop 2) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).drop 2) ((treesOfOrderSucc 3).drop 2) pageG07B03RRL pageG07B03RRR

private theorem pageG07B03R : (rootPage ((treesOfOrderSucc 3).drop 2) (treesOfOrderSucc 3)).all paidTree = true :=
  split_right (p := paidTree) 2 ((treesOfOrderSucc 3).drop 2) (treesOfOrderSucc 3) pageG07B03RL pageG07B03RR

theorem pageG07B03 : (rootPage (treesOfOrderSucc 3) (treesOfOrderSucc 3)).all paidTree = true :=
  split_left (p := paidTree) 2 (treesOfOrderSucc 3) (treesOfOrderSucc 3) pageG07B03L pageG07B03R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
