module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKCert.ReviewedNative.GradedProducts
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Two exact seven-active order-seven strict SDIRK controls -/

namespace RKResearch.Certified.SDIRKSevenTwoGhostF19

open RKResearch Graded FiniteRootedTree
open scoped Matrix
abbrev K := ZMod 19


namespace Centered

def A : Matrix (Fin 9) (Fin 9) K := !![8,0,0,0,0,0,0,0,0;
     4,8,0,0,0,0,0,0,0;
     16,13,8,0,0,0,0,0,0;
     0,16,16,8,0,0,0,0,0;
     2,10,8,16,8,0,0,0,0;
     8,8,4,12,12,8,0,0,0;
     2,11,15,17,15,16,8,0,0;
     12,3,11,6,12,1,14,8,0;
     14,16,14,10,13,5,15,12,8]
def b : Fin 9→K := ![0,0,10,10,7,7,3,18,3]
def c : Fin 9→K := ![8,12,18,2,6,14,8,10,12]
def y (i : Fin 9) : K := 12*(1-c i)

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(8:K) := by decide +kernel
theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 := by decide +kernel
theorem row_sums : A *ᵥ 1=c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 9,(A *ᵥ 1) i=c i) i
theorem distinct_active (i j : Fin 9) :
    (2 : ℕ) ≤ i.val → (2 : ℕ) ≤ j.val → y i=y j → i=j := by
  exact (by decide +kernel :
    ∀ i j : Fin 9,(2 : ℕ) ≤ i.val → (2 : ℕ) ≤ j.val → y i=y j → i=j) i j

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

def bad := (bushyTree 5).butcherProduct (bushyTree 3)

theorem bad_size : bad.order=8 := by decide +kernel

theorem bad_value : (bad.factorial:K)*(b ⬝ᵥ Φ bad A)=(10:K) := by decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h bad (by rw [bad_size]; decide)
  rw [bad_value] at e
  exact (by decide +kernel : (10:K)≠1) e

theorem strict_unit : IsUnit (8:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

theorem symmetric_arithmetic :
  y 7=6 ∧ y 8=1 ∧ y 6=2*y 7-y 8 ∧
  y 2+y 3=12 ∧ y 4+y 5=12 := by decide +kernel

end Centered

namespace Affine

def A : Matrix (Fin 9) (Fin 9) K := !![16,0,0,0,0,0,0,0,0;
     18,16,0,0,0,0,0,0,0;
     5,14,16,0,0,0,0,0,0;
     9,15,0,16,0,0,0,0,0;
     13,12,7,1,16,0,0,0,0;
     16,5,6,1,14,16,0,0,0;
     13,9,13,6,0,14,16,0,0;
     8,1,5,8,16,17,14,16,0;
     10,14,14,2,0,11,7,6,16]
def b : Fin 9→K := ![0,0,12,10,11,8,16,6,14]
def c : Fin 9→K := ![16,15,16,2,11,1,14,9,4]
def y (i : Fin 9) : K := 6*(1-c i)

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(16:K) := by decide +kernel
theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 := by decide +kernel
theorem row_sums : A *ᵥ 1=c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 9,(A *ᵥ 1) i=c i) i
theorem distinct_active (i j : Fin 9) :
    (2 : ℕ) ≤ i.val → (2 : ℕ) ≤ j.val → y i=y j → i=j := by
  exact (by decide +kernel :
    ∀ i j : Fin 9,(2 : ℕ) ≤ i.val → (2 : ℕ) ≤ j.val → y i=y j → i=j) i j

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

def bad := bushyTree 8

theorem bad_size : bad.order=8 := by decide +kernel

theorem bad_value : (bad.factorial:K)*(b ⬝ᵥ Φ bad A)=(16:K) := by decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h bad (by rw [bad_size]; decide)
  rw [bad_value] at e
  exact (by decide +kernel : (16:K)≠1) e

theorem strict_unit : IsUnit (16:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

theorem affine_zero_clocks :
    (6:K)*c 2=1 ∧ y 5=0 ∧ y 6=2*y 7-y 8 ∧ y 6≠4-y 7 := by
  decide +kernel

end Affine

end RKResearch.Certified.SDIRKSevenTwoGhostF19
