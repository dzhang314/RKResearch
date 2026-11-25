module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G06B02.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG06B02 : (rootPage (treesOfOrderSucc 2) (treesOfOrderSucc 3)).all paidTree = true := pageG06B02

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
