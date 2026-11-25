module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G05B03.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG05B03 : (rootPage (treesOfOrderSucc 3) (treesOfOrderSucc 1)).all paidTree = true := pageG05B03

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
