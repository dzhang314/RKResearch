module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G05B00.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG05B00 : (rootPage (treesOfOrderSucc 0) (treesOfOrderSucc 4)).all paidTree = true := pageG05B00

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
