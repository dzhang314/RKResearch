module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07R : (rootPage ((treesOfOrderSucc 7).drop 214) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 106 ((treesOfOrderSucc 7).drop 214) (treesOfOrderSucc 0) pageG08B07RL pageG08B07RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
