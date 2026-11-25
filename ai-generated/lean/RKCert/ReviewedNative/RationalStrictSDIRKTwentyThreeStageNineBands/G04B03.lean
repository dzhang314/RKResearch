module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G04B03.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG04B03 : (rootPage (treesOfOrderSucc 3) (treesOfOrderSucc 0)).all paidTree = true := pageG04B03

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
