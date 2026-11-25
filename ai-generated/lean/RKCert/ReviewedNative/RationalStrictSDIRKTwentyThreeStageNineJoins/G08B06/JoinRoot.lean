module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B06.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B06.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B06 : (rootPage (treesOfOrderSucc 6) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 66 (treesOfOrderSucc 6) (treesOfOrderSucc 1) pageG08B06L pageG08B06R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
