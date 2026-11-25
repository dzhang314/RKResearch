module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B02.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B02.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G06B02.Shard003

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG06B02R : (rootPage (treesOfOrderSucc 2) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 2) ((treesOfOrderSucc 3).drop 2) pageG06B02RL pageG06B02RR

theorem pageG06B02 : (rootPage (treesOfOrderSucc 2) (treesOfOrderSucc 3)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 2) (treesOfOrderSucc 3) pageG06B02L pageG06B02R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
