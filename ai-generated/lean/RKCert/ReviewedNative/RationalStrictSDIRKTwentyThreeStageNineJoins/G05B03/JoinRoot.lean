module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B03.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B03.Shard002

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG05B03 : (rootPage (treesOfOrderSucc 3) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (treesOfOrderSucc 3) (treesOfOrderSucc 1) pageG05B03L pageG05B03R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
