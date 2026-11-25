module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B04.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B04.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B04 : (rootPage (treesOfOrderSucc 4) (treesOfOrderSucc 3)).all paidTree = true :=
  split_left (p := paidTree) 7 (treesOfOrderSucc 4) (treesOfOrderSucc 3) pageG08B04L pageG08B04R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
