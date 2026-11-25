module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B04.Shard004

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B04LLLR : (rootPage ((((treesOfOrderSucc 4).take 7).take 3).drop 1) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).take 3).drop 1) ((treesOfOrderSucc 3).take 2) pageG08B04LLLRL pageG08B04LLLRR

private theorem pageG08B04LLL : (rootPage (((treesOfOrderSucc 4).take 7).take 3) ((treesOfOrderSucc 3).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 4).take 7).take 3) ((treesOfOrderSucc 3).take 2) pageG08B04LLLL pageG08B04LLLR

private theorem pageG08B04LLRL : (rootPage ((((treesOfOrderSucc 4).take 7).take 3).take 1) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 ((((treesOfOrderSucc 4).take 7).take 3).take 1) ((treesOfOrderSucc 3).drop 2) pageG08B04LLRLL pageG08B04LLRLR

private theorem pageG08B04LLRRR : (rootPage ((((treesOfOrderSucc 4).take 7).take 3).drop 1) (((treesOfOrderSucc 3).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).take 3).drop 1) (((treesOfOrderSucc 3).drop 2).drop 1) pageG08B04LLRRRL pageG08B04LLRRRR

private theorem pageG08B04LLRR : (rootPage ((((treesOfOrderSucc 4).take 7).take 3).drop 1) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 ((((treesOfOrderSucc 4).take 7).take 3).drop 1) ((treesOfOrderSucc 3).drop 2) pageG08B04LLRRL pageG08B04LLRRR

private theorem pageG08B04LLR : (rootPage (((treesOfOrderSucc 4).take 7).take 3) ((treesOfOrderSucc 3).drop 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((treesOfOrderSucc 4).take 7).take 3) ((treesOfOrderSucc 3).drop 2) pageG08B04LLRL pageG08B04LLRR

theorem pageG08B04LL : (rootPage (((treesOfOrderSucc 4).take 7).take 3) (treesOfOrderSucc 3)).all paidTree = true :=
  split_right (p := paidTree) 2 (((treesOfOrderSucc 4).take 7).take 3) (treesOfOrderSucc 3) pageG08B04LLL pageG08B04LLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
