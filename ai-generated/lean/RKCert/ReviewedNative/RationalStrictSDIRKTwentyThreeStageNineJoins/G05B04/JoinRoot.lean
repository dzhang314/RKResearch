module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B04.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B04.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B04.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B04.Shard004

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG05B04RR : (rootPage (((treesOfOrderSucc 4).drop 4).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((treesOfOrderSucc 4).drop 4).drop 4) (treesOfOrderSucc 0) pageG05B04RRL pageG05B04RRR

private theorem pageG05B04R : (rootPage ((treesOfOrderSucc 4).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 ((treesOfOrderSucc 4).drop 4) (treesOfOrderSucc 0) pageG05B04RL pageG05B04RR

theorem pageG05B04 : (rootPage (treesOfOrderSucc 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (treesOfOrderSucc 4) (treesOfOrderSucc 0) pageG05B04L pageG05B04R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
