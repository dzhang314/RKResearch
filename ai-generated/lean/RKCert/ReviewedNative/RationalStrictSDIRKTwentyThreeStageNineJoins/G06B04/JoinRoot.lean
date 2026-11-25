module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B04.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B04.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B04.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B04.Shard004

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG06B04RR : (rootPage (((treesOfOrderSucc 4).drop 4).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((treesOfOrderSucc 4).drop 4).drop 4) (treesOfOrderSucc 1) pageG06B04RRL pageG06B04RRR

private theorem pageG06B04R : (rootPage ((treesOfOrderSucc 4).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 ((treesOfOrderSucc 4).drop 4) (treesOfOrderSucc 1) pageG06B04RL pageG06B04RR

theorem pageG06B04 : (rootPage (treesOfOrderSucc 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (treesOfOrderSucc 4) (treesOfOrderSucc 1) pageG06B04L pageG06B04R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
