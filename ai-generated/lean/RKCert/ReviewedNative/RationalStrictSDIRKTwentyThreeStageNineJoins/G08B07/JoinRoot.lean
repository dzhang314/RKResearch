module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07 : (rootPage (treesOfOrderSucc 7) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 214 (treesOfOrderSucc 7) (treesOfOrderSucc 0) pageG08B07L pageG08B07R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
