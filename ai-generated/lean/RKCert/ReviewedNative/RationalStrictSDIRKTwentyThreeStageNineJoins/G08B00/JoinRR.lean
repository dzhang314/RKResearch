module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RR : (rootPage (treesOfOrderSucc 0) (((treesOfOrderSucc 7).drop 1).drop 214)).all paidTree = true :=
  split_right (p := paidTree) 106 (treesOfOrderSucc 0) (((treesOfOrderSucc 7).drop 1).drop 214) pageG08B00RRL pageG08B00RRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
