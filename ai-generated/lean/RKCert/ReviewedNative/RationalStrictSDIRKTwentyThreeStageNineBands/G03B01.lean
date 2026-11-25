module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G03B01.Shard001

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG03B01 : (rootPage (treesOfOrderSucc 1) (treesOfOrderSucc 1)).all paidTree = true := pageG03B01

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
