module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G04B03.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G04B03.Shard002

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG04B03 : (rootPage (treesOfOrderSucc 3) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (treesOfOrderSucc 3) (treesOfOrderSucc 0) pageG04B03L pageG04B03R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
