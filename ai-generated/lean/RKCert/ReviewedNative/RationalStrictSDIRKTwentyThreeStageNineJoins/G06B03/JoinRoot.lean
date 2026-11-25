module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B03.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B03.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B03.Shard003

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG06B03R : (rootPage ((treesOfOrderSucc 3).drop 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 2 ((treesOfOrderSucc 3).drop 2) (treesOfOrderSucc 2) pageG06B03RL pageG06B03RR

theorem pageG06B03 : (rootPage (treesOfOrderSucc 3) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 2 (treesOfOrderSucc 3) (treesOfOrderSucc 2) pageG06B03L pageG06B03R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
