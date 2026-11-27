module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKCert.ReviewedNative.GradedProducts
public import RKCert.Research.SDIRKSevenChristoffelScalar
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Second-active Christoffel-zero order-seven control over F19 -/

namespace RKResearch.Certified.SDIRKSevenChristoffelSecondF19

open RKResearch Graded FiniteRootedTree
open scoped Matrix
abbrev K := ZMod 19

def A : Matrix (Fin 9) (Fin 9) K := !![16,0,0,0,0,0,0,0,0;
     11,16,0,0,0,0,0,0,0;
     3,16,16,0,0,0,0,0,0;
     2,8,4,16,0,0,0,0,0;
     14,14,4,11,16,0,0,0,0;
     1,7,3,15,16,16,0,0,0;
     13,4,5,8,11,14,16,0,0;
     15,9,17,3,13,17,14,16,0;
     2,1,7,7,4,11,7,6,16]
def b : Fin 9→K := ![0,0,12,11,10,8,16,6,14]
def y (i : Fin 9) : K := 6*(1-(A *ᵥ 1) i)

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(16:K) := by decide +kernel
theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 := by decide +kernel

theorem distinct_active (i j : Fin 9) :
    (2 : ℕ) ≤ i.val → (2 : ℕ) ≤ j.val → y i=y j → i=j := by
  exact (by decide +kernel :
    ∀ i j : Fin 9,(2 : ℕ) ≤ i.val → (2 : ℕ) ≤ j.val → y i=y j → i=j) i j

theorem second_active_mass :
    y 2=5 ∧ y 3=16 ∧ (6:K)*A 1 0=9 ∧
    b 3*SDIRKSevenChristoffelScalar.kernelFour (13*y 3-1) (13*y 3-1)=4 := by
  decide +kernel

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

end RKResearch.Certified.SDIRKSevenChristoffelSecondF19
