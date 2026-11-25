module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G01B00.Shard001

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG01B00 : (rootPage (treesOfOrderSucc 0) (treesOfOrderSucc 0)).all paidTree = true := pageG01B00

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
