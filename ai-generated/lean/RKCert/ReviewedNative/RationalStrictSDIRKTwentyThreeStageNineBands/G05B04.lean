module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G05B04.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG05B04 : (rootPage (treesOfOrderSucc 4) (treesOfOrderSucc 0)).all paidTree = true := pageG05B04

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
