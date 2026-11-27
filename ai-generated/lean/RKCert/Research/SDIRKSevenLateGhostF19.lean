module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKCert.ReviewedNative.GradedProducts
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Three exact late-ghost order-seven controls over F19 -/

namespace RKResearch.Certified.SDIRKSevenLateGhostF19

open RKResearch Graded FiniteRootedTree
open scoped Matrix
abbrev K := ZMod 19

namespace Reflection

def A : Matrix (Fin 9) (Fin 9) K := !![1,0,0,0,0,0,0,0,0;
     3,1,0,0,0,0,0,0,0;
     8,4,1,0,0,0,0,0,0;
     4,2,7,1,0,0,0,0,0;
     10,5,15,18,1,0,0,0,0;
     1,10,11,16,3,1,0,0,0;
     10,5,10,12,17,18,1,0,0;
     11,15,17,17,6,10,0,1,0;
     13,16,4,18,9,8,11,15,1]
def b : Fin 9→K := ![0,0,17,3,5,0,3,5,6]
def c : Fin 9→K := ![1,4,13,14,11,4,16,1,0]

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(1:K) := by decide +kernel

theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 ∨ i=5 := by decide +kernel

theorem row_sums : A *ᵥ 1=c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 9,(A *ᵥ 1) i=c i) i

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 24000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

theorem eighth_bush_value :
    ((bushyTree 8).factorial : K) * (b ⬝ᵥ Φ (bushyTree 8) A)=2 := by
  rw [factorial_bushyTree,Φ_bushyTree,row_sums]
  decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h (bushyTree 8) (by rw [order_bushyTree]; decide)
  rw [eighth_bush_value] at e
  exact (by decide +kernel : (2:K)≠1) e

theorem common_diagonal_is_unit : IsUnit (1:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

theorem visible_third_cubic : monomialStageDefect A 2 2≠0 := by decide +kernel

theorem sixth_ghost_unpaid : Pi.single (5:Fin 9) (1:K)∉zeroSpace A 4 := by
  intro e
  have p := LinearMap.mem_ker.mp (probe_zeroSpace order_seven (k:=1) (by decide)
    (mat_zeroSpace order_seven 4 (by decide) e))
  exact (by decide +kernel :
    probe A b 1 (mat A (Pi.single (5:Fin 9) (1:K)))≠0) p

end Reflection

namespace Arithmetic

def A : Matrix (Fin 9) (Fin 9) K := !![12,0,0,0,0,0,0,0,0;
     11,12,0,0,0,0,0,0,0;
     18,17,12,0,0,0,0,0,0;
     18,12,0,12,0,0,0,0,0;
     4,5,18,5,12,0,0,0,0;
     9,11,15,10,2,12,0,0,0;
     9,9,10,11,8,10,12,0,0;
     8,5,11,5,18,11,16,12,0;
     15,6,0,3,12,0,5,12,12]
def b : Fin 9→K := ![0,0,13,2,13,0,5,11,14]
def c : Fin 9→K := ![12,4,9,4,6,2,12,10,8]

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(12:K) := by decide +kernel

theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 ∨ i=5 := by decide +kernel

theorem row_sums : A *ᵥ 1=c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 9,(A *ᵥ 1) i=c i) i

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 24000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

theorem eighth_bush_value :
    ((bushyTree 8).factorial : K) * (b ⬝ᵥ Φ (bushyTree 8) A)=2 := by
  rw [factorial_bushyTree,Φ_bushyTree,row_sums]
  decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h (bushyTree 8) (by rw [order_bushyTree]; decide)
  rw [eighth_bush_value] at e
  exact (by decide +kernel : (2:K)≠1) e

theorem common_diagonal_is_unit : IsUnit (12:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

def y (i : Fin 9) : K := 8*(1-c i)
theorem suffix_not_reflection :
    y 8=1 ∧ y 6=2*y 7-y 8 ∧ y 6≠4-y 7 := by decide +kernel

end Arithmetic

namespace Affine

def A : Matrix (Fin 9) (Fin 9) K := !![2,0,0,0,0,0,0,0,0;
     6,2,0,0,0,0,0,0,0;
     13,6,2,0,0,0,0,0,0;
     3,12,6,2,0,0,0,0,0;
     3,12,1,16,2,0,0,0,0;
     18,8,17,0,0,2,0,0,0;
     13,10,13,14,8,9,2,0,0;
     7,5,5,8,7,5,0,2,0;
     12,5,8,3,6,15,16,8,2]
def b : Fin 9→K := ![0,0,5,12,5,0,16,14,6]
def c : Fin 9→K := ![2,8,2,4,15,7,12,1,18]

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(2:K) := by decide +kernel

theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 ∨ i=5 := by decide +kernel

theorem row_sums : A *ᵥ 1=c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 9,(A *ᵥ 1) i=c i) i

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 24000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

theorem eighth_bush_value :
    ((bushyTree 8).factorial : K) * (b ⬝ᵥ Φ (bushyTree 8) A)=7 := by
  rw [factorial_bushyTree,Φ_bushyTree,row_sums]
  decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h (bushyTree 8) (by rw [order_bushyTree]; decide)
  rw [eighth_bush_value] at e
  exact (by decide +kernel : (7:K)≠1) e

theorem common_diagonal_is_unit : IsUnit (2:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

theorem first_active_one : (10:K)*c 2=1 := by decide +kernel

end Affine

end RKResearch.Certified.SDIRKSevenLateGhostF19
