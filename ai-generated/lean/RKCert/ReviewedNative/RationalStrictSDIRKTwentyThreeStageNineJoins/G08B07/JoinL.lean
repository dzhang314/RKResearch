module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07L : (rootPage ((treesOfOrderSucc 7).take 214) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 106 ((treesOfOrderSucc 7).take 214) (treesOfOrderSucc 0) pageG08B07LL pageG08B07LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
