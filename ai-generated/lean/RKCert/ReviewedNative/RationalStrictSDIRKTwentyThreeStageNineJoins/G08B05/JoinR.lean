module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B05.JoinRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B05.JoinRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B05R : (rootPage ((treesOfOrderSucc 5).drop 21) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 10 ((treesOfOrderSucc 5).drop 21) (treesOfOrderSucc 2) pageG08B05RL pageG08B05RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
