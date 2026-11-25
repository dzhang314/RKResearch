module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard020
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard021
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard022
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard023
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard024
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard025
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard026
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard027

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B07LLRRLLR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14).take 6).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14).take 6).drop 2) (treesOfOrderSucc 0) pageG08B07LLRRLLRL pageG08B07LLRRLLRR

private theorem pageG08B07LLRRLL : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14).take 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14).take 6) (treesOfOrderSucc 0) pageG08B07LLRRLLL pageG08B07LLRRLLR

private theorem pageG08B07LLRRLRL : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14).drop 6).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14).drop 6).take 4) (treesOfOrderSucc 0) pageG08B07LLRRLRLL pageG08B07LLRRLRLR

private theorem pageG08B07LLRRLRR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14).drop 6).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14).drop 6).drop 4) (treesOfOrderSucc 0) pageG08B07LLRRLRRL pageG08B07LLRRLRRR

private theorem pageG08B07LLRRLR : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14).drop 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14).drop 6) (treesOfOrderSucc 0) pageG08B07LLRRLRL pageG08B07LLRRLRR

private theorem pageG08B07LLRRL : (rootPage ((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 6 ((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).take 14) (treesOfOrderSucc 0) pageG08B07LLRRLL pageG08B07LLRRLR

private theorem pageG08B07LLRRRLR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).take 6).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).take 6).drop 2) (treesOfOrderSucc 0) pageG08B07LLRRRLRL pageG08B07LLRRRLRR

private theorem pageG08B07LLRRRL : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).take 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).take 6) (treesOfOrderSucc 0) pageG08B07LLRRRLL pageG08B07LLRRRLR

private theorem pageG08B07LLRRRRL : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).drop 6).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).drop 6).take 4) (treesOfOrderSucc 0) pageG08B07LLRRRRLL pageG08B07LLRRRRLR

private theorem pageG08B07LLRRRRR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).drop 6).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).drop 6).drop 4) (treesOfOrderSucc 0) pageG08B07LLRRRRRL pageG08B07LLRRRRRR

private theorem pageG08B07LLRRRR : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).drop 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).drop 6) (treesOfOrderSucc 0) pageG08B07LLRRRRL pageG08B07LLRRRRR

private theorem pageG08B07LLRRR : (rootPage ((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 6 ((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14) (treesOfOrderSucc 0) pageG08B07LLRRRL pageG08B07LLRRRR

theorem pageG08B07LLRR : (rootPage (((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 14 (((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26) (treesOfOrderSucc 0) pageG08B07LLRRL pageG08B07LLRRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
