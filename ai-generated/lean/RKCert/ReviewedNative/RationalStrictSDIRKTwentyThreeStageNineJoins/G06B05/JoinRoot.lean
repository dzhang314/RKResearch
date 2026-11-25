module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard008
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B05.Shard011

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG06B05LL : (rootPage (((treesOfOrderSucc 5).take 20).take 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((treesOfOrderSucc 5).take 20).take 8) (treesOfOrderSucc 0) pageG06B05LLL pageG06B05LLR

private theorem pageG06B05LRR : (rootPage ((((treesOfOrderSucc 5).take 20).drop 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 ((((treesOfOrderSucc 5).take 20).drop 8).drop 4) (treesOfOrderSucc 0) pageG06B05LRRL pageG06B05LRRR

private theorem pageG06B05LR : (rootPage (((treesOfOrderSucc 5).take 20).drop 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((treesOfOrderSucc 5).take 20).drop 8) (treesOfOrderSucc 0) pageG06B05LRL pageG06B05LRR

private theorem pageG06B05L : (rootPage ((treesOfOrderSucc 5).take 20) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 8 ((treesOfOrderSucc 5).take 20) (treesOfOrderSucc 0) pageG06B05LL pageG06B05LR

private theorem pageG06B05RL : (rootPage (((treesOfOrderSucc 5).drop 20).take 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((treesOfOrderSucc 5).drop 20).take 8) (treesOfOrderSucc 0) pageG06B05RLL pageG06B05RLR

private theorem pageG06B05RRRR : (rootPage (((((treesOfOrderSucc 5).drop 20).drop 8).drop 4).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 5).drop 20).drop 8).drop 4).drop 4) (treesOfOrderSucc 0) pageG06B05RRRRL pageG06B05RRRRR

private theorem pageG06B05RRR : (rootPage ((((treesOfOrderSucc 5).drop 20).drop 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 ((((treesOfOrderSucc 5).drop 20).drop 8).drop 4) (treesOfOrderSucc 0) pageG06B05RRRL pageG06B05RRRR

private theorem pageG06B05RR : (rootPage (((treesOfOrderSucc 5).drop 20).drop 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((treesOfOrderSucc 5).drop 20).drop 8) (treesOfOrderSucc 0) pageG06B05RRL pageG06B05RRR

private theorem pageG06B05R : (rootPage ((treesOfOrderSucc 5).drop 20) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 8 ((treesOfOrderSucc 5).drop 20) (treesOfOrderSucc 0) pageG06B05RL pageG06B05RR

theorem pageG06B05 : (rootPage (treesOfOrderSucc 5) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 20 (treesOfOrderSucc 5) (treesOfOrderSucc 0) pageG06B05L pageG06B05R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
