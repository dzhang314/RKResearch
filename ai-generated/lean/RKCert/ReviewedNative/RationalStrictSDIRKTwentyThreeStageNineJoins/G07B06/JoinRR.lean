module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard025
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard026
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard027
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard028
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard029
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard030
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard031
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard032
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B06.Shard033

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B06RRLLL : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).take 4) (treesOfOrderSucc 0) pageG07B06RRLLLL pageG07B06RRLLLR

private theorem pageG07B06RRLLR : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).drop 4) (treesOfOrderSucc 0) pageG07B06RRLLRL pageG07B06RRLLRR

private theorem pageG07B06RRLL : (rootPage (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8) (treesOfOrderSucc 0) pageG07B06RRLLL pageG07B06RRLLR

private theorem pageG07B06RRLRL : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).take 4) (treesOfOrderSucc 0) pageG07B06RRLRLL pageG07B06RRLRLR

private theorem pageG07B06RRLRR : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).drop 4) (treesOfOrderSucc 0) pageG07B06RRLRRL pageG07B06RRLRRR

private theorem pageG07B06RRLR : (rootPage (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8) (treesOfOrderSucc 0) pageG07B06RRLRL pageG07B06RRLRR

private theorem pageG07B06RRL : (rootPage ((((treesOfOrderSucc 6).drop 66).drop 32).take 16) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).drop 66).drop 32).take 16) (treesOfOrderSucc 0) pageG07B06RRLL pageG07B06RRLR

private theorem pageG07B06RRRLL : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).take 4) (treesOfOrderSucc 0) pageG07B06RRRLLL pageG07B06RRRLLR

private theorem pageG07B06RRRLR : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).drop 4) (treesOfOrderSucc 0) pageG07B06RRRLRL pageG07B06RRRLRR

private theorem pageG07B06RRRL : (rootPage (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8) (treesOfOrderSucc 0) pageG07B06RRRLL pageG07B06RRRLR

private theorem pageG07B06RRRRL : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).take 4) (treesOfOrderSucc 0) pageG07B06RRRRLL pageG07B06RRRRLR

private theorem pageG07B06RRRRRR : (rootPage (((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4).drop 2) (treesOfOrderSucc 0) pageG07B06RRRRRRL pageG07B06RRRRRRR

private theorem pageG07B06RRRRR : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 0) pageG07B06RRRRRL pageG07B06RRRRRR

private theorem pageG07B06RRRR : (rootPage (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8) (treesOfOrderSucc 0) pageG07B06RRRRL pageG07B06RRRRR

private theorem pageG07B06RRR : (rootPage ((((treesOfOrderSucc 6).drop 66).drop 32).drop 16) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).drop 66).drop 32).drop 16) (treesOfOrderSucc 0) pageG07B06RRRL pageG07B06RRRR

theorem pageG07B06RR : (rootPage (((treesOfOrderSucc 6).drop 66).drop 32) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 16 (((treesOfOrderSucc 6).drop 66).drop 32) (treesOfOrderSucc 0) pageG07B06RRL pageG07B06RRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
