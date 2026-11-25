module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G06B01.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG06B01 : (rootPage (treesOfOrderSucc 1) (treesOfOrderSucc 4)).all paidTree = true := pageG06B01

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
