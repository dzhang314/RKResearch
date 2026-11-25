module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinRRRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinRRRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07RRR : (rootPage ((((treesOfOrderSucc 7).drop 214).drop 106).drop 54) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 26 ((((treesOfOrderSucc 7).drop 214).drop 106).drop 54) (treesOfOrderSucc 0) pageG08B07RRRL pageG08B07RRRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
