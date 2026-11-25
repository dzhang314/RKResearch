module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G03B02.Shard001

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG03B02 : (rootPage (treesOfOrderSucc 2) (treesOfOrderSucc 0)).all paidTree = true := pageG03B02

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
