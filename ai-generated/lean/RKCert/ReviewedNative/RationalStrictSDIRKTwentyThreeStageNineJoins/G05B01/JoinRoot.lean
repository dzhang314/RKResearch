module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B01.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B01.Shard002

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG05B01 : (rootPage (treesOfOrderSucc 1) (treesOfOrderSucc 3)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (treesOfOrderSucc 3) pageG05B01L pageG05B01R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
