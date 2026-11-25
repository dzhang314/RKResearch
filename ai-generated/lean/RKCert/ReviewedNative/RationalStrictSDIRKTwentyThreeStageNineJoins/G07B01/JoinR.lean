module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard007
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard008
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard009
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard010
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard011

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B01RLL : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).drop 20).take 10).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).drop 20).take 10).take 4) pageG07B01RLLL pageG07B01RLLR

private theorem pageG07B01RLRR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 5).drop 20).take 10).drop 4).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) (((((treesOfOrderSucc 5).drop 20).take 10).drop 4).drop 2) pageG07B01RLRRL pageG07B01RLRRR

private theorem pageG07B01RLR : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).drop 20).take 10).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).drop 20).take 10).drop 4) pageG07B01RLRL pageG07B01RLRR

private theorem pageG07B01RL : (rootPage (treesOfOrderSucc 1) (((treesOfOrderSucc 5).drop 20).take 10)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((treesOfOrderSucc 5).drop 20).take 10) pageG07B01RLL pageG07B01RLR

private theorem pageG07B01RRLR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 5).drop 20).drop 10).take 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) (((((treesOfOrderSucc 5).drop 20).drop 10).take 6).drop 2) pageG07B01RRLRL pageG07B01RRLRR

private theorem pageG07B01RRL : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).drop 20).drop 10).take 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).drop 20).drop 10).take 6) pageG07B01RRLL pageG07B01RRLR

private theorem pageG07B01RRRR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 5).drop 20).drop 10).drop 6).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) (((((treesOfOrderSucc 5).drop 20).drop 10).drop 6).drop 2) pageG07B01RRRRL pageG07B01RRRRR

private theorem pageG07B01RRR : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).drop 20).drop 10).drop 6)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).drop 20).drop 10).drop 6) pageG07B01RRRL pageG07B01RRRR

private theorem pageG07B01RR : (rootPage (treesOfOrderSucc 1) (((treesOfOrderSucc 5).drop 20).drop 10)).all paidTree = true :=
  split_right (p := paidTree) 6 (treesOfOrderSucc 1) (((treesOfOrderSucc 5).drop 20).drop 10) pageG07B01RRL pageG07B01RRR

theorem pageG07B01R : (rootPage (treesOfOrderSucc 1) ((treesOfOrderSucc 5).drop 20)).all paidTree = true :=
  split_right (p := paidTree) 10 (treesOfOrderSucc 1) ((treesOfOrderSucc 5).drop 20) pageG07B01RL pageG07B01RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
