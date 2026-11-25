module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RRR : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 7).drop 1).drop 214).drop 106)).all paidTree = true :=
  split_right (p := paidTree) 54 (treesOfOrderSucc 0) ((((treesOfOrderSucc 7).drop 1).drop 214).drop 106) pageG08B00RRRL pageG08B00RRRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
