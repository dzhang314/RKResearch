module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G05B02.Shard001

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG05B02 : (rootPage (treesOfOrderSucc 2) (treesOfOrderSucc 2)).all paidTree = true := pageG05B02

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
