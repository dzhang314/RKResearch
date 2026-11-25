module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G04B01.Shard001

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG04B01 : (rootPage (treesOfOrderSucc 1) (treesOfOrderSucc 2)).all paidTree = true := pageG04B01

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
