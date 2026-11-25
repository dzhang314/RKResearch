module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G06B04.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG06B04 : (rootPage (treesOfOrderSucc 4) (treesOfOrderSucc 1)).all paidTree = true := pageG06B04

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
