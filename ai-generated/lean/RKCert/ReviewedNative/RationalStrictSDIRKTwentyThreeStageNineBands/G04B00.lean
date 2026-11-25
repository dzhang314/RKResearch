module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G04B00.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG04B00 : (rootPage (treesOfOrderSucc 0) (treesOfOrderSucc 3)).all paidTree = true := pageG04B00

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
