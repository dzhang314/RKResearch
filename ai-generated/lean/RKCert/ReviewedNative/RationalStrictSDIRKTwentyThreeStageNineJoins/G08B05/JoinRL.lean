module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard011
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard012
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard013
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard014
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard015
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard016

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B05RLLL : (rootPage (((((treesOfOrderSucc 5).drop 21).take 10).take 5).take 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).drop 21).take 10).take 5).take 2) (treesOfOrderSucc 2) pageG08B05RLLLL pageG08B05RLLLR

private theorem pageG08B05RLLRR : (rootPage ((((((treesOfOrderSucc 5).drop 21).take 10).take 5).drop 2).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((((treesOfOrderSucc 5).drop 21).take 10).take 5).drop 2).drop 1) (treesOfOrderSucc 2) pageG08B05RLLRRL pageG08B05RLLRRR

private theorem pageG08B05RLLR : (rootPage (((((treesOfOrderSucc 5).drop 21).take 10).take 5).drop 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).drop 21).take 10).take 5).drop 2) (treesOfOrderSucc 2) pageG08B05RLLRL pageG08B05RLLRR

private theorem pageG08B05RLL : (rootPage ((((treesOfOrderSucc 5).drop 21).take 10).take 5) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).drop 21).take 10).take 5) (treesOfOrderSucc 2) pageG08B05RLLL pageG08B05RLLR

private theorem pageG08B05RLRL : (rootPage (((((treesOfOrderSucc 5).drop 21).take 10).drop 5).take 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).drop 21).take 10).drop 5).take 2) (treesOfOrderSucc 2) pageG08B05RLRLL pageG08B05RLRLR

private theorem pageG08B05RLRRR : (rootPage ((((((treesOfOrderSucc 5).drop 21).take 10).drop 5).drop 2).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((((treesOfOrderSucc 5).drop 21).take 10).drop 5).drop 2).drop 1) (treesOfOrderSucc 2) pageG08B05RLRRRL pageG08B05RLRRRR

private theorem pageG08B05RLRR : (rootPage (((((treesOfOrderSucc 5).drop 21).take 10).drop 5).drop 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).drop 21).take 10).drop 5).drop 2) (treesOfOrderSucc 2) pageG08B05RLRRL pageG08B05RLRRR

private theorem pageG08B05RLR : (rootPage ((((treesOfOrderSucc 5).drop 21).take 10).drop 5) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).drop 21).take 10).drop 5) (treesOfOrderSucc 2) pageG08B05RLRL pageG08B05RLRR

theorem pageG08B05RL : (rootPage (((treesOfOrderSucc 5).drop 21).take 10) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 5 (((treesOfOrderSucc 5).drop 21).take 10) (treesOfOrderSucc 2) pageG08B05RLL pageG08B05RLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
