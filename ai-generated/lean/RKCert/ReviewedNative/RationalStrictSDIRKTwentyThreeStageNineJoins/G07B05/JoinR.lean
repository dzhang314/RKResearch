module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard008
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard011

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B05RLL : (rootPage ((((treesOfOrderSucc 5).drop 20).take 10).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).drop 20).take 10).take 4) (treesOfOrderSucc 1) pageG07B05RLLL pageG07B05RLLR

private theorem pageG07B05RLRR : (rootPage (((((treesOfOrderSucc 5).drop 20).take 10).drop 4).drop 2) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((treesOfOrderSucc 5).drop 20).take 10).drop 4).drop 2) (treesOfOrderSucc 1) pageG07B05RLRRL pageG07B05RLRRR

private theorem pageG07B05RLR : (rootPage ((((treesOfOrderSucc 5).drop 20).take 10).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).drop 20).take 10).drop 4) (treesOfOrderSucc 1) pageG07B05RLRL pageG07B05RLRR

private theorem pageG07B05RL : (rootPage (((treesOfOrderSucc 5).drop 20).take 10) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((treesOfOrderSucc 5).drop 20).take 10) (treesOfOrderSucc 1) pageG07B05RLL pageG07B05RLR

private theorem pageG07B05RRLR : (rootPage (((((treesOfOrderSucc 5).drop 20).drop 10).take 6).drop 2) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((treesOfOrderSucc 5).drop 20).drop 10).take 6).drop 2) (treesOfOrderSucc 1) pageG07B05RRLRL pageG07B05RRLRR

private theorem pageG07B05RRL : (rootPage ((((treesOfOrderSucc 5).drop 20).drop 10).take 6) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).drop 20).drop 10).take 6) (treesOfOrderSucc 1) pageG07B05RRLL pageG07B05RRLR

private theorem pageG07B05RRRR : (rootPage (((((treesOfOrderSucc 5).drop 20).drop 10).drop 6).drop 2) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((treesOfOrderSucc 5).drop 20).drop 10).drop 6).drop 2) (treesOfOrderSucc 1) pageG07B05RRRRL pageG07B05RRRRR

private theorem pageG07B05RRR : (rootPage ((((treesOfOrderSucc 5).drop 20).drop 10).drop 6) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).drop 20).drop 10).drop 6) (treesOfOrderSucc 1) pageG07B05RRRL pageG07B05RRRR

private theorem pageG07B05RR : (rootPage (((treesOfOrderSucc 5).drop 20).drop 10) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 6 (((treesOfOrderSucc 5).drop 20).drop 10) (treesOfOrderSucc 1) pageG07B05RRL pageG07B05RRR

theorem pageG07B05R : (rootPage ((treesOfOrderSucc 5).drop 20) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 10 ((treesOfOrderSucc 5).drop 20) (treesOfOrderSucc 1) pageG07B05RL pageG07B05RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
