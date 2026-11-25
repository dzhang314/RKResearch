module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard008
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B00.Shard011

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG06B00LL : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 5).take 20).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((treesOfOrderSucc 5).take 20).take 8) pageG06B00LLL pageG06B00LLR

private theorem pageG06B00LRR : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 5).take 20).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) ((((treesOfOrderSucc 5).take 20).drop 8).drop 4) pageG06B00LRRL pageG06B00LRRR

private theorem pageG06B00LR : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 5).take 20).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((treesOfOrderSucc 5).take 20).drop 8) pageG06B00LRL pageG06B00LRR

private theorem pageG06B00L : (rootPage (treesOfOrderSucc 0) ((treesOfOrderSucc 5).take 20)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 0) ((treesOfOrderSucc 5).take 20) pageG06B00LL pageG06B00LR

private theorem pageG06B00RL : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 5).drop 20).take 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((treesOfOrderSucc 5).drop 20).take 8) pageG06B00RLL pageG06B00RLR

private theorem pageG06B00RRRR : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 5).drop 20).drop 8).drop 4).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((((treesOfOrderSucc 5).drop 20).drop 8).drop 4).drop 4) pageG06B00RRRRL pageG06B00RRRRR

private theorem pageG06B00RRR : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 5).drop 20).drop 8).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) ((((treesOfOrderSucc 5).drop 20).drop 8).drop 4) pageG06B00RRRL pageG06B00RRRR

private theorem pageG06B00RR : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 5).drop 20).drop 8)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((treesOfOrderSucc 5).drop 20).drop 8) pageG06B00RRL pageG06B00RRR

private theorem pageG06B00R : (rootPage (treesOfOrderSucc 0) ((treesOfOrderSucc 5).drop 20)).all paidTree = true :=
  split_right (p := paidTree) 8 (treesOfOrderSucc 0) ((treesOfOrderSucc 5).drop 20) pageG06B00RL pageG06B00RR

theorem pageG06B00 : (rootPage (treesOfOrderSucc 0) (treesOfOrderSucc 5)).all paidTree = true :=
  split_right (p := paidTree) 20 (treesOfOrderSucc 0) (treesOfOrderSucc 5) pageG06B00L pageG06B00R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
