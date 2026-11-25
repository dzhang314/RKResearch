module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B01.JoinRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B01.JoinRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B01R : (rootPage (treesOfOrderSucc 1) ((treesOfOrderSucc 6).drop 66)).all paidTree = true :=
  split_right (p := paidTree) 32 (treesOfOrderSucc 1) ((treesOfOrderSucc 6).drop 66) pageG08B01RL pageG08B01RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
