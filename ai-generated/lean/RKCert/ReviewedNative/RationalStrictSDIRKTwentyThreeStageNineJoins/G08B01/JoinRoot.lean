module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B01.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B01.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B01 : (rootPage (treesOfOrderSucc 1) (treesOfOrderSucc 6)).all paidTree = true :=
  split_right (p := paidTree) 66 (treesOfOrderSucc 1) (treesOfOrderSucc 6) pageG08B01L pageG08B01R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
