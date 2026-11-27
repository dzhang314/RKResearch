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

namespace RKResearch.Certified.SDIRKSevenMultiplierZeroF19

open RKResearch Graded FiniteRootedTree
open scoped Matrix BigOperators
abbrev K := ZMod 19

namespace Second

def A : Matrix (Fin 9) (Fin 9) K := !![13,0,0,0,0,0,0,0,0;
     9,13,0,0,0,0,0,0,0;
     9,9,13,0,0,0,0,0,0;
     4,11,13,13,0,0,0,0,0;
     6,8,7,6,13,0,0,0,0;
     6,17,8,15,9,13,0,0,0;
     15,11,9,6,4,13,13,0,0;
     15,12,2,16,3,14,2,13,0;
     11,1,11,13,5,12,16,1,13]
def b : Fin 9→K := ![0,0,7,12,5,10,10,2,12]
def V : Fin 9→K := ![0,0,16,0,2,1,6,8,8]
def B : Matrix (Fin 9) (Fin 9) K := (3:K) • A
def x : Fin 9→K := B *ᵥ 1
def Y (i : Fin 9) : K := 3-x i
def W (y : K) : K := 18+16*y
def cubic (i : Fin 9) : K := (B *ᵥ (B *ᵥ x)) i - 16*(x i)^3
def D (i : Fin 9) : K := 10*b i*(Y i)^2-(∑ j, b j*Y j*B j i)
def activeDeriv (i : Fin 9) : K :=
  ∏ j ∈ (Finset.univ.filter fun j : Fin 9 => 2≤ j.val ∧ j≠i), (Y i-Y j)

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(13:K) := by decide +kernel
theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 := by decide +kernel

theorem distinct_active : ∀ i j : Fin 9,
    (2:ℕ)≤ i.val → (2:ℕ)≤ j.val → Y i=Y j → i=j := by decide +kernel

theorem active_adjoint : ∀ i : Fin 9, (2:ℕ)≤ i.val →
    D i*activeDeriv i=15*W (Y i) ∧ W (Y i)≠0 := by decide +kernel

theorem cubic_direction : ∀ i : Fin 9, (2:ℕ)≤ i.val →
    cubic i=10*V i := by decide +kernel

theorem multiplier_site :
    Y 3=13 ∧ (∀ i : Fin 9,(2:ℕ)≤ i.val → (V i=0 ↔ i=3)) ∧
    b 3*SDIRKSevenChristoffelScalar.kernelFour (7*Y 3-1) (7*Y 3-1)≠4 := by
  decide +kernel

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

def bad := bushyTree 8

theorem bad_size : bad.order=8 := by decide +kernel
theorem bad_value : (bad.factorial:K)*(b ⬝ᵥ Φ bad A)=(2:K) := by decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h bad (by rw [bad_size]; decide)
  rw [bad_value] at e
  exact (by decide +kernel : (2:K)≠1) e

theorem strict_unit : IsUnit (13:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

end Second

namespace Fourth

def A : Matrix (Fin 9) (Fin 9) K := !![14,0,0,0,0,0,0,0,0;
     18,14,0,0,0,0,0,0,0;
     10,13,14,0,0,0,0,0,0;
     6,17,1,14,0,0,0,0,0;
     18,1,13,2,14,0,0,0,0;
     15,13,11,4,4,14,0,0,0;
     17,13,9,14,4,13,14,0,0;
     13,17,11,15,14,14,4,14,0;
     2,15,12,3,10,11,6,9,14]
def b : Fin 9→K := ![0,0,11,5,5,4,11,1,2]
def V : Fin 9→K := ![0,0,17,8,12,0,16,7,12]
def B : Matrix (Fin 9) (Fin 9) K := (15:K) • A
def x : Fin 9→K := B *ᵥ 1
def Y (i : Fin 9) : K := 15-x i
def W (y : K) : K := 0+16*y
def cubic (i : Fin 9) : K := (B *ᵥ (B *ᵥ x)) i - 16*(x i)^3
def D (i : Fin 9) : K := 10*b i*(Y i)^2-(∑ j, b j*Y j*B j i)
def activeDeriv (i : Fin 9) : K :=
  ∏ j ∈ (Finset.univ.filter fun j : Fin 9 => 2≤ j.val ∧ j≠i), (Y i-Y j)

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(14:K) := by decide +kernel
theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 := by decide +kernel

theorem distinct_active : ∀ i j : Fin 9,
    (2:ℕ)≤ i.val → (2:ℕ)≤ j.val → Y i=Y j → i=j := by decide +kernel

theorem active_adjoint : ∀ i : Fin 9, (2:ℕ)≤ i.val →
    D i*activeDeriv i=6*W (Y i) ∧ W (Y i)≠0 := by decide +kernel

theorem cubic_direction : ∀ i : Fin 9, (2:ℕ)≤ i.val →
    cubic i=2*V i := by decide +kernel

theorem multiplier_site :
    Y 5=12 ∧ (∀ i : Fin 9,(2:ℕ)≤ i.val → (V i=0 ↔ i=5)) ∧
    b 5*SDIRKSevenChristoffelScalar.kernelFour (9*Y 5-1) (9*Y 5-1)≠4 := by
  decide +kernel

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

def bad := bushyTree 8

theorem bad_size : bad.order=8 := by decide +kernel
theorem bad_value : (bad.factorial:K)*(b ⬝ᵥ Φ bad A)=(12:K) := by decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h bad (by rw [bad_size]; decide)
  rw [bad_value] at e
  exact (by decide +kernel : (12:K)≠1) e

theorem strict_unit : IsUnit (14:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

end Fourth

end RKResearch.Certified.SDIRKSevenMultiplierZeroF19
