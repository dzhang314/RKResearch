module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G04B02.Shard001

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG04B02 : (rootPage (treesOfOrderSucc 2) (treesOfOrderSucc 1)).all paidTree = true := pageG04B02

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
