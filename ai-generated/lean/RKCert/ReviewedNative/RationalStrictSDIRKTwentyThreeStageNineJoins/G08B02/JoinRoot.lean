module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B02.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B02.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B02 : (rootPage (treesOfOrderSucc 2) (treesOfOrderSucc 5)).all paidTree = true :=
  split_right (p := paidTree) 21 (treesOfOrderSucc 2) (treesOfOrderSucc 5) pageG08B02L pageG08B02R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
