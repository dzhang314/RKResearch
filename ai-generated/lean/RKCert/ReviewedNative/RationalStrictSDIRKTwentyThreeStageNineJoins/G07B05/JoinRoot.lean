module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B05.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B05.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG07B05 : (rootPage (treesOfOrderSucc 5) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 20 (treesOfOrderSucc 5) (treesOfOrderSucc 1) pageG07B05L pageG07B05R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
