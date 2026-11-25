module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B03.Shard004

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B03LLLR : (rootPage ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).take 7).take 3).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) ((((treesOfOrderSucc 4).take 7).take 3).drop 1) pageG08B03LLLRL pageG08B03LLLRR

private theorem pageG08B03LLL : (rootPage ((treesOfOrderSucc 3).take 2) (((treesOfOrderSucc 4).take 7).take 3)).all paidTree = true :=
  split_right (p := paidTree) 1 ((treesOfOrderSucc 3).take 2) (((treesOfOrderSucc 4).take 7).take 3) pageG08B03LLLL pageG08B03LLLR

private theorem pageG08B03LLRL : (rootPage (((treesOfOrderSucc 3).drop 2).take 1) (((treesOfOrderSucc 4).take 7).take 3)).all paidTree = true :=
  split_right (p := paidTree) 2 (((treesOfOrderSucc 3).drop 2).take 1) (((treesOfOrderSucc 4).take 7).take 3) pageG08B03LLRLL pageG08B03LLRLR

private theorem pageG08B03LLRRR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).take 7).take 3).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) ((((treesOfOrderSucc 4).take 7).take 3).drop 1) pageG08B03LLRRRL pageG08B03LLRRRR

private theorem pageG08B03LLRR : (rootPage (((treesOfOrderSucc 3).drop 2).drop 1) (((treesOfOrderSucc 4).take 7).take 3)).all paidTree = true :=
  split_right (p := paidTree) 1 (((treesOfOrderSucc 3).drop 2).drop 1) (((treesOfOrderSucc 4).take 7).take 3) pageG08B03LLRRL pageG08B03LLRRR

private theorem pageG08B03LLR : (rootPage ((treesOfOrderSucc 3).drop 2) (((treesOfOrderSucc 4).take 7).take 3)).all paidTree = true :=
  split_left (p := paidTree) 1 ((treesOfOrderSucc 3).drop 2) (((treesOfOrderSucc 4).take 7).take 3) pageG08B03LLRL pageG08B03LLRR

theorem pageG08B03LL : (rootPage (treesOfOrderSucc 3) (((treesOfOrderSucc 4).take 7).take 3)).all paidTree = true :=
  split_left (p := paidTree) 2 (treesOfOrderSucc 3) (((treesOfOrderSucc 4).take 7).take 3) pageG08B03LLL pageG08B03LLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
