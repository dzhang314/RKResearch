module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKCert.ReviewedNative.GradedProducts
public import RKCert.Research.SDIRKSevenChristoffelScalar
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Exact nine-stage order-seven controls; physical active profiles -/

namespace RKResearch.Certified.SDIRKSevenQuarticPoleF19

open RKResearch Graded FiniteRootedTree
open scoped Matrix BigOperators
abbrev K := ZMod 19

namespace Reflection

def A : Matrix (Fin 9) (Fin 9) K := !![10,0,0,0,0,0,0,0,0;
     5,10,0,0,0,0,0,0,0;
     15,2,10,0,0,0,0,0,0;
     14,8,8,10,0,0,0,0,0;
     13,16,12,12,10,0,0,0,0;
     2,18,11,5,18,10,0,0,0;
     10,8,5,12,18,12,10,0,0;
     10,17,11,7,3,0,0,10,0;
     9,6,9,1,17,5,7,3,10]
def b : Fin 9→K := ![0,0,10,13,12,18,6,14,4]
def V : Fin 9→K := ![0,0,9,9,3,5,5,16,10]
def B : Matrix (Fin 9) (Fin 9) K := (2:K) • A
def x : Fin 9→K := B *ᵥ 1
def Y (i : Fin 9) : K := 2-x i
def W (y : K) : K := 16+1*y
def cubic (i : Fin 9) : K := (B *ᵥ (B *ᵥ x)) i - 16*(x i)^3
def D (i : Fin 9) : K := 10*b i*(Y i)^2-(∑ j, b j*Y j*B j i)
def activeDeriv (i : Fin 9) : K :=
  ∏ j ∈ (Finset.univ.filter fun j : Fin 9 => 2≤ j.val ∧ j≠i), (Y i-Y j)

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(10:K) := by decide +kernel
theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 := by decide +kernel

theorem distinct_active : ∀ i j : Fin 9,
    (2:ℕ)≤ i.val → (2:ℕ)≤ j.val → Y i=Y j → i=j := by decide +kernel

theorem active_adjoint : ∀ i : Fin 9, (2:ℕ)≤ i.val →
    D i*activeDeriv i=18*W (Y i) ∧ W (Y i)≠0 := by decide +kernel

theorem cubic_direction : ∀ i : Fin 9, (2:ℕ)≤ i.val →
    cubic i=1*V i := by decide +kernel
def g (y : K) : K := 9*y^0+1*y^1+18*y^2+8*y^3+1*y^4
theorem quartic_profile : ∀ i : Fin 9, (2:ℕ)≤ i.val →
    W (Y i)*V i=g (Y i) ∧ V i≠0 := by decide +kernel

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

def bad := bushyTree 8

theorem bad_size : bad.order=8 := by decide +kernel
theorem bad_value : (bad.factorial:K)*(b ⬝ᵥ Φ bad A)=(9:K) := by decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h bad (by rw [bad_size]; decide)
  rw [bad_value] at e
  exact (by decide +kernel : (9:K)≠1) e

theorem strict_unit : IsUnit (10:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

end Reflection

namespace Arithmetic

def A : Matrix (Fin 9) (Fin 9) K := !![1,0,0,0,0,0,0,0,0;
     8,1,0,0,0,0,0,0,0;
     16,8,1,0,0,0,0,0,0;
     18,12,5,1,0,0,0,0,0;
     14,16,4,14,1,0,0,0,0;
     17,1,9,2,5,1,0,0,0;
     16,9,4,3,10,15,1,0,0;
     2,2,14,0,18,16,14,1,0;
     4,5,11,12,3,5,13,3,1]
def b : Fin 9→K := ![0,0,4,4,13,4,7,16,10]
def V : Fin 9→K := ![0,0,5,6,15,2,17,15,4]
def B : Matrix (Fin 9) (Fin 9) K := (1:K) • A
def x : Fin 9→K := B *ᵥ 1
def Y (i : Fin 9) : K := 1-x i
def W (y : K) : K := 1+1*y
def cubic (i : Fin 9) : K := (B *ᵥ (B *ᵥ x)) i - 16*(x i)^3
def D (i : Fin 9) : K := 10*b i*(Y i)^2-(∑ j, b j*Y j*B j i)
def activeDeriv (i : Fin 9) : K :=
  ∏ j ∈ (Finset.univ.filter fun j : Fin 9 => 2≤ j.val ∧ j≠i), (Y i-Y j)

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(1:K) := by decide +kernel
theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 := by decide +kernel

theorem distinct_active : ∀ i j : Fin 9,
    (2:ℕ)≤ i.val → (2:ℕ)≤ j.val → Y i=Y j → i=j := by decide +kernel

theorem active_adjoint : ∀ i : Fin 9, (2:ℕ)≤ i.val →
    D i*activeDeriv i=18*W (Y i) ∧ W (Y i)≠0 := by decide +kernel

theorem cubic_direction : ∀ i : Fin 9, (2:ℕ)≤ i.val →
    cubic i=4*V i := by decide +kernel
def g (y : K) : K := 17*y^0+0*y^1+6*y^2+3*y^3+1*y^4
theorem quartic_profile : ∀ i : Fin 9, (2:ℕ)≤ i.val →
    W (Y i)*V i=g (Y i) ∧ V i≠0 := by decide +kernel

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

def bad := bushyTree 8

theorem bad_size : bad.order=8 := by decide +kernel
theorem bad_value : (bad.factorial:K)*(b ⬝ᵥ Φ bad A)=(8:K) := by decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h bad (by rw [bad_size]; decide)
  rw [bad_value] at e
  exact (by decide +kernel : (8:K)≠1) e

theorem strict_unit : IsUnit (1:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

end Arithmetic

end RKResearch.Certified.SDIRKSevenQuarticPoleF19
