module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B03.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B03.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B03 : (rootPage (treesOfOrderSucc 3) (treesOfOrderSucc 4)).all paidTree = true :=
  split_right (p := paidTree) 7 (treesOfOrderSucc 3) (treesOfOrderSucc 4) pageG08B03L pageG08B03R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
