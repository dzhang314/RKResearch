module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Seeds and literal eleven-stage SDIRK8 modulo 31² -/

namespace RKResearch.Certified.SDIRKEightEleven31Lift

open RKResearch FiniteRootedTree
open scoped Matrix BigOperators

theorem t_place_nonsquare : ∀ d : ZMod 11, d^2 ≠ (6 : ZMod 11) := by decide +kernel
theorem c_place_nonsquare : ∀ d : ZMod 13, d^2 ≠ (8 : ZMod 13) := by decide +kernel

theorem simple_31_seed :
    (11 : ZMod 31)^3-9*(11:ZMod 31)^2+18*11-6=0 ∧
    (17 : ZMod 31)^2-14*17+11=0 ∧
    (4 : ZMod 31)^2+19*4+1=0 ∧
    (3*(11:ZMod 31)^2-18*11+18 ≠ 0) ∧
    (2*(17:ZMod 31)-14 ≠ 0) ∧
    (2*(4:ZMod 31)+19 ≠ 0) := by decide +kernel

abbrev K := ZMod 961

def A : Matrix (Fin 11) (Fin 11) K := !![538,0,0,0,0,0,0,0,0,0,0;
  923,538,0,0,0,0,0,0,0,0,0;
  454,431,538,0,0,0,0,0,0,0,0;
  231,476,947,538,0,0,0,0,0,0,0;
  178,395,152,151,538,0,0,0,0,0,0;
  838,926,482,402,106,538,0,0,0,0,0;
  123,554,435,414,865,378,538,0,0,0,0;
  432,705,856,456,819,915,239,538,0,0,0;
  356,157,519,140,259,903,677,795,538,0,0;
  87,778,702,815,931,438,175,136,667,538,0;
  230,81,666,433,316,321,800,759,578,507,538]
def b : Fin 11 → K := ![0,0,609,0,177,385,813,928,472,609,813]

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 11,A i i=(538:K) := by decide +kernel

theorem strict_unit : IsUnit (538:K) :=
  ⟨⟨538, 234, by decide +kernel, by decide +kernel⟩, rfl⟩

def bad := bushyTree 9

theorem bad_size : bad.order=9 := by decide +kernel
theorem bad_read : b ⬝ᵥ Φ bad A=(684:K) := by decide +kernel
theorem bad_scaled : (bad.factorial:K)*(b ⬝ᵥ Φ bad A)=(390:K) := by decide +kernel

theorem not_order_nine : ¬HasOrder 9 A b := by
  intro h
  have e := h bad (by rw [bad_size]; decide)
  rw [bad_scaled] at e
  exact (by decide +kernel : (390:K) ≠ 1) e

theorem literal_shape_and_failure :
    A.IsLowerTriangular ∧ (∀ i : Fin 11,A i i=(538:K)) ∧ IsUnit (538:K) ∧
      ¬HasOrder 9 A b :=
  ⟨lower_triangular,diagonal,strict_unit,not_order_nine⟩

end RKResearch.Certified.SDIRKEightEleven31Lift
