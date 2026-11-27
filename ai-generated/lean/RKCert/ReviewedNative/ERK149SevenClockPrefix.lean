module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import RKCert.ReviewedNative.PaidDefectBridge
public import Mathlib.Algebra.Field.Rat

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.ERK149SevenClockPrefix

open RKResearch RKResearch.FiniteRootedTree
open RKResearch.Certified.PaidDefectBridge (treeSize treeGrade forestNat)
open scoped Matrix FiniteRootedTree

def A0 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![0,0,0,0,0,0,0,0,0;
     (1/3),0,0,0,0,0,0,0,0;
     0,(2/3),0,0,0,0,0,0,0;
     (1/12),(1/3),-(1/12),0,0,0,0,0,0;
     (7/4),-9,(9/4),6,0,0,0,0,0;
     -(3/64),(9/8),-(9/64),-(27/64),-(1/64),0,0,0,0;
     -(65/4),81,(9/4),-33,-1,-32,0,0,0;
     (11/120),0,(27/40),(27/40),(1/12),-(8/15),(1/120),0,0;
     (193/1920),0,(81/640),(351/640),-(7/192),-(4/15),-(7/1920),(1/32),0]

def decoder : Matrix (Fin 5) (Fin 9) ℚ :=
  !![1,0,0,0,0,0,0,0,0;
     -(15/2),0,(27/2),27,0,-16,0,-1,-16;
     20,0,-81,-(243/2),-5,80,-(1/2),12,96;
     -(45/2),0,(297/2),(351/2),15,-128,(3/2),-30,-160;
     9,0,-81,-81,-10,64,-1,20,80]

def residual (t : FiniteRootedTree) (j : Fin 7) : ℚ :=
  (if j.val = treeGrade t then (forestNat t : ℚ)⁻¹ else 0) -
    (if h : j.val < 5 then (decoder *ᵥ Φ t A0) ⟨j.val,h⟩ else 0)

def shape₀ : Fin 7 → ℚ := ![0,1/2,-(3/2),1,0,0,0]
def shape₁ : Fin 7 → ℚ := ![0,0,-(1/2),2,-(5/2),1,0]

def atZero (t : FiniteRootedTree) : Bool :=
  decide (residual t 0 = 0)
def allZero (t : FiniteRootedTree) : Bool :=
  (List.finRange 7).all fun j => decide (residual t j = 0)
def inSourceSix (t : FiniteRootedTree) : Bool :=
  (List.finRange 7).all fun j => decide (residual t j =
    2 * residual t 1 * shape₀ j + residual t 5 * shape₁ j)
def atOne (t : FiniteRootedTree) : Bool :=
  decide (∑ j : Fin 7, residual t j = 0)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
private theorem lowCheck :
    (List.range 5).all (fun n => (treesOfOrderSucc n).all allZero) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
private theorem sourceSixCheck :
    (treesOfOrderSucc 5).all inSourceSix = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
private theorem sourceSevenCheck :
    (treesOfOrderSucc 6).all atOne = true := by
  decide +kernel

theorem lowExact (t : FiniteRootedTree) (ht : treeSize t ≤ 5) (j : Fin 7) :
    residual t j = 0 := by
  have hm : t ∈ treesOfOrderSucc (treeSize t - 1) := by
    apply (mem_treesOfOrderSucc _ _).mpr
    have hp : 0 < treeSize t := t.order.pos
    exact (Nat.sub_add_cancel (show 1 ≤ treeSize t from hp)).symm
  have hx := List.all_eq_true.mp lowCheck (treeSize t - 1) (List.mem_range.mpr (by omega))
  have hh := List.all_eq_true.mp hx t hm
  exact of_decide_eq_true (List.all_eq_true.mp hh j (List.mem_finRange j))

theorem sourceSix (t : FiniteRootedTree) (ht : treeSize t = 6) (j : Fin 7) :
    residual t j = 2 * residual t 1 * shape₀ j + residual t 5 * shape₁ j := by
  have hm : t ∈ treesOfOrderSucc 5 := (mem_treesOfOrderSucc _ _).mpr ht
  have hh := List.all_eq_true.mp sourceSixCheck t hm
  exact of_decide_eq_true (List.all_eq_true.mp hh j (List.mem_finRange j))

theorem sourceSevenAtOne (t : FiniteRootedTree) (ht : treeSize t = 7) :
    ∑ j : Fin 7, residual t j = 0 := by
  exact of_decide_eq_true (List.all_eq_true.mp sourceSevenCheck t
    ((mem_treesOfOrderSucc _ _).mpr ht))

end RKResearch.Certified.ERK149SevenClockPrefix
