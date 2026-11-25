module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinLRLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinLRLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07LRL : (rootPage ((((treesOfOrderSucc 7).take 214).drop 106).take 54) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 26 ((((treesOfOrderSucc 7).take 214).drop 106).take 54) (treesOfOrderSucc 0) pageG08B07LRLL pageG08B07LRLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
