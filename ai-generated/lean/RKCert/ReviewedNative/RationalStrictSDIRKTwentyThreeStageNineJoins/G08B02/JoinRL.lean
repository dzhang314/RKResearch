module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard011
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard012
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard013
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard014
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard015
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard016

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B02RLLL : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).take 10).take 5).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).take 10).take 5).take 2) pageG08B02RLLLL pageG08B02RLLLR

private theorem pageG08B02RLLRR : (rootPage (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).drop 21).take 10).take 5).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).drop 21).take 10).take 5).drop 2).drop 1) pageG08B02RLLRRL pageG08B02RLLRRR

private theorem pageG08B02RLLR : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).take 10).take 5).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).take 10).take 5).drop 2) pageG08B02RLLRL pageG08B02RLLRR

private theorem pageG08B02RLL : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).drop 21).take 10).take 5)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).drop 21).take 10).take 5) pageG08B02RLLL pageG08B02RLLR

private theorem pageG08B02RLRL : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).take 10).drop 5).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).take 10).drop 5).take 2) pageG08B02RLRLL pageG08B02RLRLR

private theorem pageG08B02RLRRR : (rootPage (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).drop 21).take 10).drop 5).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).drop 21).take 10).drop 5).drop 2).drop 1) pageG08B02RLRRRL pageG08B02RLRRRR

private theorem pageG08B02RLRR : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).take 10).drop 5).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).drop 21).take 10).drop 5).drop 2) pageG08B02RLRRL pageG08B02RLRRR

private theorem pageG08B02RLR : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).drop 21).take 10).drop 5)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).drop 21).take 10).drop 5) pageG08B02RLRL pageG08B02RLRR

theorem pageG08B02RL : (rootPage (treesOfOrderSucc 2) (((treesOfOrderSucc 5).drop 21).take 10)).all paidTree = true :=
  split_right (p := paidTree) 5 (treesOfOrderSucc 2) (((treesOfOrderSucc 5).drop 21).take 10) pageG08B02RLL pageG08B02RLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
