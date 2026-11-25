module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B00.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B00.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B00.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B00.Shard004

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG05B00RR : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 4).drop 4).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (((treesOfOrderSucc 4).drop 4).drop 4) pageG05B00RRL pageG05B00RRR

private theorem pageG05B00R : (rootPage (treesOfOrderSucc 0) ((treesOfOrderSucc 4).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) ((treesOfOrderSucc 4).drop 4) pageG05B00RL pageG05B00RR

theorem pageG05B00 : (rootPage (treesOfOrderSucc 0) (treesOfOrderSucc 4)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (treesOfOrderSucc 4) pageG05B00L pageG05B00R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
