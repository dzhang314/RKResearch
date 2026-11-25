module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinRRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinRRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07RR : (rootPage (((treesOfOrderSucc 7).drop 214).drop 106) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 54 (((treesOfOrderSucc 7).drop 214).drop 106) (treesOfOrderSucc 0) pageG08B07RRL pageG08B07RRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
