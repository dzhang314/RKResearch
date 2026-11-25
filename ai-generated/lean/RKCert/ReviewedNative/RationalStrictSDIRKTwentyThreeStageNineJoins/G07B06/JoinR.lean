module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B06.JoinRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B06.JoinRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG07B06R : (rootPage ((treesOfOrderSucc 6).drop 66) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 32 ((treesOfOrderSucc 6).drop 66) (treesOfOrderSucc 0) pageG07B06RL pageG07B06RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
