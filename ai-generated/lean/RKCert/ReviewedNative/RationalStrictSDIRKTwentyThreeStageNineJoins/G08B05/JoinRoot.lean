module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B05.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B05.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B05 : (rootPage (treesOfOrderSucc 5) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 21 (treesOfOrderSucc 5) (treesOfOrderSucc 2) pageG08B05L pageG08B05R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
