module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G02B01.Shard001

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG02B01 : (rootPage (treesOfOrderSucc 1) (treesOfOrderSucc 0)).all paidTree = true := pageG02B01

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
