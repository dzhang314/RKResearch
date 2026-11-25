module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G05B01.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG05B01 : (rootPage (treesOfOrderSucc 1) (treesOfOrderSucc 3)).all paidTree = true := pageG05B01

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
