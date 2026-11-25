module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G06B00.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG06B00 : (rootPage (treesOfOrderSucc 0) (treesOfOrderSucc 5)).all paidTree = true := pageG06B00

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
