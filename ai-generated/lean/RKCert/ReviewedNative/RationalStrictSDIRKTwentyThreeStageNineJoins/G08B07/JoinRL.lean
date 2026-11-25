module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinRLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinRLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07RL : (rootPage (((treesOfOrderSucc 7).drop 214).take 106) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 52 (((treesOfOrderSucc 7).drop 214).take 106) (treesOfOrderSucc 0) pageG08B07RLL pageG08B07RLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
