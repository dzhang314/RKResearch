module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B05.JoinRoot

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidBandG07B05 : (rootPage (treesOfOrderSucc 5) (treesOfOrderSucc 1)).all paidTree = true := pageG07B05

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
