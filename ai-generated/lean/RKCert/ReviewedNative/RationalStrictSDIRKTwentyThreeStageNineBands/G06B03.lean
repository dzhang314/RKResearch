module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G06B03.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG06B03 : (rootPage (treesOfOrderSucc 3) (treesOfOrderSucc 2)).all paidTree = true := pageG06B03

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
