module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B02.JoinRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B02.JoinRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B02R : (rootPage (treesOfOrderSucc 2) ((treesOfOrderSucc 5).drop 21)).all paidTree = true :=
  split_right (p := paidTree) 10 (treesOfOrderSucc 2) ((treesOfOrderSucc 5).drop 21) pageG08B02RL pageG08B02RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
