module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G02B00.Shard001

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG02B00 : (rootPage (treesOfOrderSucc 0) (treesOfOrderSucc 1)).all paidTree = true := pageG02B00

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
