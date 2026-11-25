module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B04.JoinRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B04.JoinRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B04R : (rootPage ((treesOfOrderSucc 4).drop 7) (treesOfOrderSucc 3)).all paidTree = true :=
  split_left (p := paidTree) 3 ((treesOfOrderSucc 4).drop 7) (treesOfOrderSucc 3) pageG08B04RL pageG08B04RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
