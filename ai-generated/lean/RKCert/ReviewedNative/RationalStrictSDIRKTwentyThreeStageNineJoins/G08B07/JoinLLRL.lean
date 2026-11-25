module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard014
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard015
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard016
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard017
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard018
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard019
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard020

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B07LLRLLLR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).take 12).take 6).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).take 12).take 6).drop 2) (treesOfOrderSucc 0) pageG08B07LLRLLLRL pageG08B07LLRLLLRR

private theorem pageG08B07LLRLLL : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).take 12).take 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).take 12).take 6) (treesOfOrderSucc 0) pageG08B07LLRLLLL pageG08B07LLRLLLR

private theorem pageG08B07LLRLLRR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).take 12).drop 6).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).take 12).drop 6).drop 2) (treesOfOrderSucc 0) pageG08B07LLRLLRRL pageG08B07LLRLLRRR

private theorem pageG08B07LLRLLR : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).take 12).drop 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).take 12).drop 6) (treesOfOrderSucc 0) pageG08B07LLRLLRL pageG08B07LLRLLRR

private theorem pageG08B07LLRLL : (rootPage ((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).take 12) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 6 ((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).take 12) (treesOfOrderSucc 0) pageG08B07LLRLLL pageG08B07LLRLLR

private theorem pageG08B07LLRLRLR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12).take 6).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12).take 6).drop 2) (treesOfOrderSucc 0) pageG08B07LLRLRLRL pageG08B07LLRLRLRR

private theorem pageG08B07LLRLRL : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12).take 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12).take 6) (treesOfOrderSucc 0) pageG08B07LLRLRLL pageG08B07LLRLRLR

private theorem pageG08B07LLRLRRL : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12).drop 6).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12).drop 6).take 4) (treesOfOrderSucc 0) pageG08B07LLRLRRLL pageG08B07LLRLRRLR

private theorem pageG08B07LLRLRRR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12).drop 6).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12).drop 6).drop 4) (treesOfOrderSucc 0) pageG08B07LLRLRRRL pageG08B07LLRLRRRR

private theorem pageG08B07LLRLRR : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12).drop 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12).drop 6) (treesOfOrderSucc 0) pageG08B07LLRLRRL pageG08B07LLRLRRR

private theorem pageG08B07LLRLR : (rootPage ((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 6 ((((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26).drop 12) (treesOfOrderSucc 0) pageG08B07LLRLRL pageG08B07LLRLRR

theorem pageG08B07LLRL : (rootPage (((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 12 (((((treesOfOrderSucc 7).take 214).take 106).drop 52).take 26) (treesOfOrderSucc 0) pageG08B07LLRLL pageG08B07LLRLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
