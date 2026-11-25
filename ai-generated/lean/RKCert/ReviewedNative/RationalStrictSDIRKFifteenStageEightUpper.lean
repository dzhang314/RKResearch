module

public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightCore
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightTall
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch01
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch02
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch03
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch04
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch05
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch06
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch07
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch08
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch09
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch10
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch11
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch12
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch13
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch14
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch15
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch16
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch17
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch18
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch19
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch20
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch21
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch22
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch23
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch24
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch25
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch26
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch27
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch28
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch29
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch30
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch31
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch32
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch33
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch34
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch35
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch36
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch37
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch38
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch39
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch40
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch41
public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightBatches.Batch42

import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKFifteenStageEightUpper

open FiniteRootedTree
open scoped Matrix

private theorem paidGroup4 : (treesOfOrderSucc 4).all paidTree = true :=
  all_true_parts 8 (treesOfOrderSucc 4) paidGroup4L paidGroup4R

private theorem paidGroup5LR : (((treesOfOrderSucc 5).take 24).drop 8).all paidTree = true :=
  all_true_parts 8 (((treesOfOrderSucc 5).take 24).drop 8) paidGroup5LRL paidGroup5LRR

private theorem paidGroup5L : ((treesOfOrderSucc 5).take 24).all paidTree = true :=
  all_true_parts 8 ((treesOfOrderSucc 5).take 24) paidGroup5LL paidGroup5LR

private theorem paidGroup5RR : (((treesOfOrderSucc 5).drop 24).drop 8).all paidTree = true :=
  all_true_parts 8 (((treesOfOrderSucc 5).drop 24).drop 8) paidGroup5RRL paidGroup5RRR

private theorem paidGroup5R : ((treesOfOrderSucc 5).drop 24).all paidTree = true :=
  all_true_parts 8 ((treesOfOrderSucc 5).drop 24) paidGroup5RL paidGroup5RR

private theorem paidGroup5 : (treesOfOrderSucc 5).all paidTree = true :=
  all_true_parts 24 (treesOfOrderSucc 5) paidGroup5L paidGroup5R

private theorem paidGroup6LLL : ((((treesOfOrderSucc 6).take 64).take 32).take 16).all paidTree = true :=
  all_true_parts 8 ((((treesOfOrderSucc 6).take 64).take 32).take 16) paidGroup6LLLL paidGroup6LLLR

private theorem paidGroup6LLR : ((((treesOfOrderSucc 6).take 64).take 32).drop 16).all paidTree = true :=
  all_true_parts 8 ((((treesOfOrderSucc 6).take 64).take 32).drop 16) paidGroup6LLRL paidGroup6LLRR

private theorem paidGroup6LL : (((treesOfOrderSucc 6).take 64).take 32).all paidTree = true :=
  all_true_parts 16 (((treesOfOrderSucc 6).take 64).take 32) paidGroup6LLL paidGroup6LLR

private theorem paidGroup6LRL : ((((treesOfOrderSucc 6).take 64).drop 32).take 16).all paidTree = true :=
  all_true_parts 8 ((((treesOfOrderSucc 6).take 64).drop 32).take 16) paidGroup6LRLL paidGroup6LRLR

private theorem paidGroup6LRR : ((((treesOfOrderSucc 6).take 64).drop 32).drop 16).all paidTree = true :=
  all_true_parts 8 ((((treesOfOrderSucc 6).take 64).drop 32).drop 16) paidGroup6LRRL paidGroup6LRRR

private theorem paidGroup6LR : (((treesOfOrderSucc 6).take 64).drop 32).all paidTree = true :=
  all_true_parts 16 (((treesOfOrderSucc 6).take 64).drop 32) paidGroup6LRL paidGroup6LRR

private theorem paidGroup6L : ((treesOfOrderSucc 6).take 64).all paidTree = true :=
  all_true_parts 32 ((treesOfOrderSucc 6).take 64) paidGroup6LL paidGroup6LR

private theorem paidGroup6RLL : ((((treesOfOrderSucc 6).drop 64).take 32).take 16).all paidTree = true :=
  all_true_parts 8 ((((treesOfOrderSucc 6).drop 64).take 32).take 16) paidGroup6RLLL paidGroup6RLLR

private theorem paidGroup6RLR : ((((treesOfOrderSucc 6).drop 64).take 32).drop 16).all paidTree = true :=
  all_true_parts 8 ((((treesOfOrderSucc 6).drop 64).take 32).drop 16) paidGroup6RLRL paidGroup6RLRR

private theorem paidGroup6RL : (((treesOfOrderSucc 6).drop 64).take 32).all paidTree = true :=
  all_true_parts 16 (((treesOfOrderSucc 6).drop 64).take 32) paidGroup6RLL paidGroup6RLR

private theorem paidGroup6RRL : ((((treesOfOrderSucc 6).drop 64).drop 32).take 16).all paidTree = true :=
  all_true_parts 8 ((((treesOfOrderSucc 6).drop 64).drop 32).take 16) paidGroup6RRLL paidGroup6RRLR

private theorem paidGroup6RRRR : (((((treesOfOrderSucc 6).drop 64).drop 32).drop 16).drop 8).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 6).drop 64).drop 32).drop 16).drop 8) paidGroup6RRRRL paidGroup6RRRRR

private theorem paidGroup6RRR : ((((treesOfOrderSucc 6).drop 64).drop 32).drop 16).all paidTree = true :=
  all_true_parts 8 ((((treesOfOrderSucc 6).drop 64).drop 32).drop 16) paidGroup6RRRL paidGroup6RRRR

private theorem paidGroup6RR : (((treesOfOrderSucc 6).drop 64).drop 32).all paidTree = true :=
  all_true_parts 16 (((treesOfOrderSucc 6).drop 64).drop 32) paidGroup6RRL paidGroup6RRR

private theorem paidGroup6R : ((treesOfOrderSucc 6).drop 64).all paidTree = true :=
  all_true_parts 32 ((treesOfOrderSucc 6).drop 64) paidGroup6RL paidGroup6RR

private theorem paidGroup6 : (treesOfOrderSucc 6).all paidTree = true :=
  all_true_parts 64 (treesOfOrderSucc 6) paidGroup6L paidGroup6R

private theorem paidGroup7LLLLR : ((((((treesOfOrderSucc 7).take 216).take 104).take 48).take 24).drop 8).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).take 104).take 48).take 24).drop 8) paidGroup7LLLLRL paidGroup7LLLLRR

private theorem paidGroup7LLLL : (((((treesOfOrderSucc 7).take 216).take 104).take 48).take 24).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 7).take 216).take 104).take 48).take 24) paidGroup7LLLLL paidGroup7LLLLR

private theorem paidGroup7LLLRR : ((((((treesOfOrderSucc 7).take 216).take 104).take 48).drop 24).drop 8).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).take 104).take 48).drop 24).drop 8) paidGroup7LLLRRL paidGroup7LLLRRR

private theorem paidGroup7LLLR : (((((treesOfOrderSucc 7).take 216).take 104).take 48).drop 24).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 7).take 216).take 104).take 48).drop 24) paidGroup7LLLRL paidGroup7LLLRR

private theorem paidGroup7LLL : ((((treesOfOrderSucc 7).take 216).take 104).take 48).all paidTree = true :=
  all_true_parts 24 ((((treesOfOrderSucc 7).take 216).take 104).take 48) paidGroup7LLLL paidGroup7LLLR

private theorem paidGroup7LLRLR : ((((((treesOfOrderSucc 7).take 216).take 104).drop 48).take 24).drop 8).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).take 104).drop 48).take 24).drop 8) paidGroup7LLRLRL paidGroup7LLRLRR

private theorem paidGroup7LLRL : (((((treesOfOrderSucc 7).take 216).take 104).drop 48).take 24).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 7).take 216).take 104).drop 48).take 24) paidGroup7LLRLL paidGroup7LLRLR

private theorem paidGroup7LLRRL : ((((((treesOfOrderSucc 7).take 216).take 104).drop 48).drop 24).take 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).take 104).drop 48).drop 24).take 16) paidGroup7LLRRLL paidGroup7LLRRLR

private theorem paidGroup7LLRRR : ((((((treesOfOrderSucc 7).take 216).take 104).drop 48).drop 24).drop 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).take 104).drop 48).drop 24).drop 16) paidGroup7LLRRRL paidGroup7LLRRRR

private theorem paidGroup7LLRR : (((((treesOfOrderSucc 7).take 216).take 104).drop 48).drop 24).all paidTree = true :=
  all_true_parts 16 (((((treesOfOrderSucc 7).take 216).take 104).drop 48).drop 24) paidGroup7LLRRL paidGroup7LLRRR

private theorem paidGroup7LLR : ((((treesOfOrderSucc 7).take 216).take 104).drop 48).all paidTree = true :=
  all_true_parts 24 ((((treesOfOrderSucc 7).take 216).take 104).drop 48) paidGroup7LLRL paidGroup7LLRR

private theorem paidGroup7LL : (((treesOfOrderSucc 7).take 216).take 104).all paidTree = true :=
  all_true_parts 48 (((treesOfOrderSucc 7).take 216).take 104) paidGroup7LLL paidGroup7LLR

private theorem paidGroup7LRLLR : ((((((treesOfOrderSucc 7).take 216).drop 104).take 56).take 24).drop 8).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).drop 104).take 56).take 24).drop 8) paidGroup7LRLLRL paidGroup7LRLLRR

private theorem paidGroup7LRLL : (((((treesOfOrderSucc 7).take 216).drop 104).take 56).take 24).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 7).take 216).drop 104).take 56).take 24) paidGroup7LRLLL paidGroup7LRLLR

private theorem paidGroup7LRLRL : ((((((treesOfOrderSucc 7).take 216).drop 104).take 56).drop 24).take 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).drop 104).take 56).drop 24).take 16) paidGroup7LRLRLL paidGroup7LRLRLR

private theorem paidGroup7LRLRR : ((((((treesOfOrderSucc 7).take 216).drop 104).take 56).drop 24).drop 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).drop 104).take 56).drop 24).drop 16) paidGroup7LRLRRL paidGroup7LRLRRR

private theorem paidGroup7LRLR : (((((treesOfOrderSucc 7).take 216).drop 104).take 56).drop 24).all paidTree = true :=
  all_true_parts 16 (((((treesOfOrderSucc 7).take 216).drop 104).take 56).drop 24) paidGroup7LRLRL paidGroup7LRLRR

private theorem paidGroup7LRL : ((((treesOfOrderSucc 7).take 216).drop 104).take 56).all paidTree = true :=
  all_true_parts 24 ((((treesOfOrderSucc 7).take 216).drop 104).take 56) paidGroup7LRLL paidGroup7LRLR

private theorem paidGroup7LRRLR : ((((((treesOfOrderSucc 7).take 216).drop 104).drop 56).take 24).drop 8).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).drop 104).drop 56).take 24).drop 8) paidGroup7LRRLRL paidGroup7LRRLRR

private theorem paidGroup7LRRL : (((((treesOfOrderSucc 7).take 216).drop 104).drop 56).take 24).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 7).take 216).drop 104).drop 56).take 24) paidGroup7LRRLL paidGroup7LRRLR

private theorem paidGroup7LRRRL : ((((((treesOfOrderSucc 7).take 216).drop 104).drop 56).drop 24).take 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).drop 104).drop 56).drop 24).take 16) paidGroup7LRRRLL paidGroup7LRRRLR

private theorem paidGroup7LRRRR : ((((((treesOfOrderSucc 7).take 216).drop 104).drop 56).drop 24).drop 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).take 216).drop 104).drop 56).drop 24).drop 16) paidGroup7LRRRRL paidGroup7LRRRRR

private theorem paidGroup7LRRR : (((((treesOfOrderSucc 7).take 216).drop 104).drop 56).drop 24).all paidTree = true :=
  all_true_parts 16 (((((treesOfOrderSucc 7).take 216).drop 104).drop 56).drop 24) paidGroup7LRRRL paidGroup7LRRRR

private theorem paidGroup7LRR : ((((treesOfOrderSucc 7).take 216).drop 104).drop 56).all paidTree = true :=
  all_true_parts 24 ((((treesOfOrderSucc 7).take 216).drop 104).drop 56) paidGroup7LRRL paidGroup7LRRR

private theorem paidGroup7LR : (((treesOfOrderSucc 7).take 216).drop 104).all paidTree = true :=
  all_true_parts 56 (((treesOfOrderSucc 7).take 216).drop 104) paidGroup7LRL paidGroup7LRR

private theorem paidGroup7L : ((treesOfOrderSucc 7).take 216).all paidTree = true :=
  all_true_parts 104 ((treesOfOrderSucc 7).take 216) paidGroup7LL paidGroup7LR

private theorem paidGroup7RLLLR : ((((((treesOfOrderSucc 7).drop 216).take 104).take 48).take 24).drop 8).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).take 104).take 48).take 24).drop 8) paidGroup7RLLLRL paidGroup7RLLLRR

private theorem paidGroup7RLLL : (((((treesOfOrderSucc 7).drop 216).take 104).take 48).take 24).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 7).drop 216).take 104).take 48).take 24) paidGroup7RLLLL paidGroup7RLLLR

private theorem paidGroup7RLLRR : ((((((treesOfOrderSucc 7).drop 216).take 104).take 48).drop 24).drop 8).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).take 104).take 48).drop 24).drop 8) paidGroup7RLLRRL paidGroup7RLLRRR

private theorem paidGroup7RLLR : (((((treesOfOrderSucc 7).drop 216).take 104).take 48).drop 24).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 7).drop 216).take 104).take 48).drop 24) paidGroup7RLLRL paidGroup7RLLRR

private theorem paidGroup7RLL : ((((treesOfOrderSucc 7).drop 216).take 104).take 48).all paidTree = true :=
  all_true_parts 24 ((((treesOfOrderSucc 7).drop 216).take 104).take 48) paidGroup7RLLL paidGroup7RLLR

private theorem paidGroup7RLRLR : ((((((treesOfOrderSucc 7).drop 216).take 104).drop 48).take 24).drop 8).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).take 104).drop 48).take 24).drop 8) paidGroup7RLRLRL paidGroup7RLRLRR

private theorem paidGroup7RLRL : (((((treesOfOrderSucc 7).drop 216).take 104).drop 48).take 24).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 7).drop 216).take 104).drop 48).take 24) paidGroup7RLRLL paidGroup7RLRLR

private theorem paidGroup7RLRRL : ((((((treesOfOrderSucc 7).drop 216).take 104).drop 48).drop 24).take 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).take 104).drop 48).drop 24).take 16) paidGroup7RLRRLL paidGroup7RLRRLR

private theorem paidGroup7RLRRR : ((((((treesOfOrderSucc 7).drop 216).take 104).drop 48).drop 24).drop 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).take 104).drop 48).drop 24).drop 16) paidGroup7RLRRRL paidGroup7RLRRRR

private theorem paidGroup7RLRR : (((((treesOfOrderSucc 7).drop 216).take 104).drop 48).drop 24).all paidTree = true :=
  all_true_parts 16 (((((treesOfOrderSucc 7).drop 216).take 104).drop 48).drop 24) paidGroup7RLRRL paidGroup7RLRRR

private theorem paidGroup7RLR : ((((treesOfOrderSucc 7).drop 216).take 104).drop 48).all paidTree = true :=
  all_true_parts 24 ((((treesOfOrderSucc 7).drop 216).take 104).drop 48) paidGroup7RLRL paidGroup7RLRR

private theorem paidGroup7RL : (((treesOfOrderSucc 7).drop 216).take 104).all paidTree = true :=
  all_true_parts 48 (((treesOfOrderSucc 7).drop 216).take 104) paidGroup7RLL paidGroup7RLR

private theorem paidGroup7RRLLR : ((((((treesOfOrderSucc 7).drop 216).drop 104).take 56).take 24).drop 8).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).drop 104).take 56).take 24).drop 8) paidGroup7RRLLRL paidGroup7RRLLRR

private theorem paidGroup7RRLL : (((((treesOfOrderSucc 7).drop 216).drop 104).take 56).take 24).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 7).drop 216).drop 104).take 56).take 24) paidGroup7RRLLL paidGroup7RRLLR

private theorem paidGroup7RRLRL : ((((((treesOfOrderSucc 7).drop 216).drop 104).take 56).drop 24).take 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).drop 104).take 56).drop 24).take 16) paidGroup7RRLRLL paidGroup7RRLRLR

private theorem paidGroup7RRLRR : ((((((treesOfOrderSucc 7).drop 216).drop 104).take 56).drop 24).drop 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).drop 104).take 56).drop 24).drop 16) paidGroup7RRLRRL paidGroup7RRLRRR

private theorem paidGroup7RRLR : (((((treesOfOrderSucc 7).drop 216).drop 104).take 56).drop 24).all paidTree = true :=
  all_true_parts 16 (((((treesOfOrderSucc 7).drop 216).drop 104).take 56).drop 24) paidGroup7RRLRL paidGroup7RRLRR

private theorem paidGroup7RRL : ((((treesOfOrderSucc 7).drop 216).drop 104).take 56).all paidTree = true :=
  all_true_parts 24 ((((treesOfOrderSucc 7).drop 216).drop 104).take 56) paidGroup7RRLL paidGroup7RRLR

private theorem paidGroup7RRRLR : ((((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).take 24).drop 8).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).take 24).drop 8) paidGroup7RRRLRL paidGroup7RRRLRR

private theorem paidGroup7RRRL : (((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).take 24).all paidTree = true :=
  all_true_parts 8 (((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).take 24) paidGroup7RRRLL paidGroup7RRRLR

private theorem paidGroup7RRRRL : ((((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).drop 24).take 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).drop 24).take 16) paidGroup7RRRRLL paidGroup7RRRRLR

private theorem paidGroup7RRRRR : ((((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).drop 24).drop 16).all paidTree = true :=
  all_true_parts 8 ((((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).drop 24).drop 16) paidGroup7RRRRRL paidGroup7RRRRRR

private theorem paidGroup7RRRR : (((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).drop 24).all paidTree = true :=
  all_true_parts 16 (((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).drop 24) paidGroup7RRRRL paidGroup7RRRRR

private theorem paidGroup7RRR : ((((treesOfOrderSucc 7).drop 216).drop 104).drop 56).all paidTree = true :=
  all_true_parts 24 ((((treesOfOrderSucc 7).drop 216).drop 104).drop 56) paidGroup7RRRL paidGroup7RRRR

private theorem paidGroup7RR : (((treesOfOrderSucc 7).drop 216).drop 104).all paidTree = true :=
  all_true_parts 56 (((treesOfOrderSucc 7).drop 216).drop 104) paidGroup7RRL paidGroup7RRR

private theorem paidGroup7R : ((treesOfOrderSucc 7).drop 216).all paidTree = true :=
  all_true_parts 104 ((treesOfOrderSucc 7).drop 216) paidGroup7RL paidGroup7RR

private theorem paidGroup7 : (treesOfOrderSucc 7).all paidTree = true :=
  all_true_parts 216 (treesOfOrderSucc 7) paidGroup7L paidGroup7R

private theorem paidGroup (n : Fin 8) :
    (treesOfOrderSucc n.val).all paidTree = true := by
  fin_cases n
  · exact paidGroup0
  · exact paidGroup1
  · exact paidGroup2
  · exact paidGroup3
  · exact paidGroup4
  · exact paidGroup5
  · exact paidGroup6
  · exact paidGroup7

private theorem checked : checkScaledOrder actInt outInt 1540104384000 33075 8 = true := by
  change (List.range 8).all (fun n => (treesOfOrderSucc n).all paidTree) = true
  apply List.all_eq_true.mpr
  intro n hn
  exact paidGroup ⟨n, List.mem_range.mp hn⟩

theorem order_eight : HasOrder 8 A b :=
  hasOrder_of_scaled_check (A := AInt) (b := bInt) (d := 1540104384000) (e := 33075) (p := 8)
    (Int.castRingHom ℚ) actInt_eq outInt_eq cast_AInt cast_bInt
    (isUnit_iff_ne_zero.mpr (by decide +kernel))
    (isUnit_iff_ne_zero.mpr (by decide +kernel)) checked

end RKResearch.Certified.RationalStrictSDIRKFifteenStageEightUpper

namespace RKResearch.Certified

/-- Fifteen rational stages suffice for exact order eight, with diagonal one eighth. -/
theorem exists_fifteen_stage_rational_strictSDIRK_exact_eight :
    ∃ (A : Matrix (Fin 15) (Fin 15) ℚ) (b : Fin 15 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/8) ∧ (1/8 : ℚ) ≠ 0 ∧
        HasOrder 8 A b ∧ ¬ HasOrder 9 A b :=
  ⟨RationalStrictSDIRKFifteenStageEightUpper.A, RationalStrictSDIRKFifteenStageEightUpper.b,
    RationalStrictSDIRKFifteenStageEightUpper.lowerTriangular,
    RationalStrictSDIRKFifteenStageEightUpper.common_diagonal, by decide +kernel,
    RationalStrictSDIRKFifteenStageEightUpper.order_eight,
    RationalStrictSDIRKFifteenStageEightUpper.not_order_nine⟩

end RKResearch.Certified
