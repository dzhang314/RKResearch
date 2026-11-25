module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B05.Shard005

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B05LLLL : (rootPage (((((treesOfOrderSucc 5).take 21).take 10).take 5).take 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).take 21).take 10).take 5).take 2) (treesOfOrderSucc 2) pageG08B05LLLLL pageG08B05LLLLR

private theorem pageG08B05LLLRR : (rootPage ((((((treesOfOrderSucc 5).take 21).take 10).take 5).drop 2).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((((treesOfOrderSucc 5).take 21).take 10).take 5).drop 2).drop 1) (treesOfOrderSucc 2) pageG08B05LLLRRL pageG08B05LLLRRR

private theorem pageG08B05LLLR : (rootPage (((((treesOfOrderSucc 5).take 21).take 10).take 5).drop 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).take 21).take 10).take 5).drop 2) (treesOfOrderSucc 2) pageG08B05LLLRL pageG08B05LLLRR

private theorem pageG08B05LLL : (rootPage ((((treesOfOrderSucc 5).take 21).take 10).take 5) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).take 21).take 10).take 5) (treesOfOrderSucc 2) pageG08B05LLLL pageG08B05LLLR

private theorem pageG08B05LLRL : (rootPage (((((treesOfOrderSucc 5).take 21).take 10).drop 5).take 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).take 21).take 10).drop 5).take 2) (treesOfOrderSucc 2) pageG08B05LLRLL pageG08B05LLRLR

private theorem pageG08B05LLRRR : (rootPage ((((((treesOfOrderSucc 5).take 21).take 10).drop 5).drop 2).drop 1) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 ((((((treesOfOrderSucc 5).take 21).take 10).drop 5).drop 2).drop 1) (treesOfOrderSucc 2) pageG08B05LLRRRL pageG08B05LLRRRR

private theorem pageG08B05LLRR : (rootPage (((((treesOfOrderSucc 5).take 21).take 10).drop 5).drop 2) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (((((treesOfOrderSucc 5).take 21).take 10).drop 5).drop 2) (treesOfOrderSucc 2) pageG08B05LLRRL pageG08B05LLRRR

private theorem pageG08B05LLR : (rootPage ((((treesOfOrderSucc 5).take 21).take 10).drop 5) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).take 21).take 10).drop 5) (treesOfOrderSucc 2) pageG08B05LLRL pageG08B05LLRR

theorem pageG08B05LL : (rootPage (((treesOfOrderSucc 5).take 21).take 10) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 5 (((treesOfOrderSucc 5).take 21).take 10) (treesOfOrderSucc 2) pageG08B05LLL pageG08B05LLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
