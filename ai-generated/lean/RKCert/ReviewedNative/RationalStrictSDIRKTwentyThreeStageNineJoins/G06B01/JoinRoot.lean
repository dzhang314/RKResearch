module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B01.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B01.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B01.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B01.Shard004

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG06B01RR : (rootPage (treesOfOrderSucc 1) (((treesOfOrderSucc 4).drop 4).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((treesOfOrderSucc 4).drop 4).drop 4) pageG06B01RRL pageG06B01RRR

private theorem pageG06B01R : (rootPage (treesOfOrderSucc 1) ((treesOfOrderSucc 4).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) ((treesOfOrderSucc 4).drop 4) pageG06B01RL pageG06B01RR

theorem pageG06B01 : (rootPage (treesOfOrderSucc 1) (treesOfOrderSucc 4)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (treesOfOrderSucc 4) pageG06B01L pageG06B01R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
