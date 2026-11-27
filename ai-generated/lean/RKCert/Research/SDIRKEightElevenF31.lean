module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Literal exact-order-eight strict SDIRK witness on eleven stages over F31 -/

namespace RKResearch.Certified.SDIRKEightElevenF31

open RKResearch FiniteRootedTree
open scoped Matrix BigOperators

abbrev K := ZMod 31

def A : Matrix (Fin 11) (Fin 11) K := !![11,0,0,0,0,0,0,0,0,0,0;
  24,11,0,0,0,0,0,0,0,0,0;
  20,28,11,0,0,0,0,0,0,0,0;
  14,11,17,11,0,0,0,0,0,0,0;
  23,23,28,27,11,0,0,0,0,0,0;
  1,27,17,30,13,11,0,0,0,0,0;
  30,27,1,11,28,6,11,0,0,0,0;
  29,23,19,22,13,16,22,11,0,0,0;
  15,2,23,16,11,4,26,20,11,0,0;
  25,3,20,9,1,4,20,12,16,11,0;
  13,19,15,30,6,11,25,15,20,11,11]
def b : Fin 11 → K := ![0,0,20,0,22,13,7,29,7,20,7]

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 11, A i i = (11 : K) := by decide +kernel

theorem strict_unit : IsUnit (11:K) := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

set_option maxHeartbeats 26000000 in
set_option maxRecDepth 37000 in
theorem order_eight : HasOrder 8 A b := by
  apply (checkOrder_iff A b 8).mp
  decide +kernel

def bad := bushyTree 9

theorem bad_size : bad.order=9 := by decide +kernel
theorem bad_read : b ⬝ᵥ Φ bad A=(2:K) := by decide +kernel
theorem bad_scaled : (bad.factorial:K)*(b ⬝ᵥ Φ bad A)=(18:K) := by decide +kernel

theorem not_order_nine : ¬HasOrder 9 A b := by
  intro h
  have e := h bad (by rw [bad_size]; decide)
  rw [bad_scaled] at e
  exact (by decide +kernel : (18:K)≠1) e

theorem literal_strict_exact_eight :
    A.IsLowerTriangular ∧ (∀ i : Fin 11, A i i=(11:K)) ∧ IsUnit (11:K) ∧
      HasOrder 8 A b ∧ ¬HasOrder 9 A b :=
  ⟨lower_triangular,diagonal,strict_unit,order_eight,not_order_nine⟩

end RKResearch.Certified.SDIRKEightElevenF31
