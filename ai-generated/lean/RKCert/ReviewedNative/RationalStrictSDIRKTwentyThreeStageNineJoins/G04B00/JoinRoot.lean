module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G04B00.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G04B00.Shard002

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG04B00 : (rootPage (treesOfOrderSucc 0) (treesOfOrderSucc 3)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 0) (treesOfOrderSucc 3) pageG04B00L pageG04B00R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
