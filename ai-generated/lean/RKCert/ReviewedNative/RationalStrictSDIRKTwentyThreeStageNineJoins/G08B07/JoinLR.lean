module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinLRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinLRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07LR : (rootPage (((treesOfOrderSucc 7).take 214).drop 106) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 54 (((treesOfOrderSucc 7).take 214).drop 106) (treesOfOrderSucc 0) pageG08B07LRL pageG08B07LRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
