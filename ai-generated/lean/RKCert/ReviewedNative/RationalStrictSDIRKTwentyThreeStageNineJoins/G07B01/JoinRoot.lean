module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B01.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B01.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG07B01 : (rootPage (treesOfOrderSucc 1) (treesOfOrderSucc 5)).all paidTree = true :=
  split_right (p := paidTree) 20 (treesOfOrderSucc 1) (treesOfOrderSucc 5) pageG07B01L pageG07B01R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
