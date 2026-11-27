module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKCert.ReviewedNative.GradedProducts
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # An arithmetic affine-helper late-ghost control over F19 -/

namespace RKResearch.Certified.SDIRKSevenLateArithmeticAffineF19

open RKResearch Graded FiniteRootedTree
open scoped Matrix
abbrev K := ZMod 19



def A : Matrix (Fin 9) (Fin 9) K := !![3,0,0,0,0,0,0,0,0;
     5,3,0,0,0,0,0,0,0;
     18,1,3,0,0,0,0,0,0;
     1,4,16,3,0,0,0,0,0;
     7,11,14,7,3,0,0,0,0;
     3,17,10,7,9,3,0,0,0;
     14,1,12,12,2,1,3,0,0;
     14,2,2,10,7,0,12,3,0;
     0,18,0,18,18,17,2,17,3]
def b : Fin 9→K := ![0,0,13,13,6,0,1,15,10]
def c : Fin 9→K := ![3,8,3,5,4,11,7,12,17]

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(3:K) := by decide +kernel

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
    ((bushyTree 8).factorial : K) * (b ⬝ᵥ Φ (bushyTree 8) A)=9 := by
  rw [factorial_bushyTree,Φ_bushyTree,row_sums]
  decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h (bushyTree 8) (by rw [order_bushyTree]; decide)
  rw [eighth_bush_value] at e
  exact (by decide +kernel : (9:K)≠1) e

theorem common_diagonal_is_unit : IsUnit (3:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

def y (i : Fin 9) : K := 13*(1-c i)
theorem suffix_not_reflection :
    y 8=1 ∧ y 6=2*y 7-y 8 ∧ y 6≠4-y 7 := by decide +kernel


theorem first_active_one : (13:K)*c 2=1 := by decide +kernel

theorem visible_opening : monomialStageDefect A 2 2≠0 := by decide +kernel

end RKResearch.Certified.SDIRKSevenLateArithmeticAffineF19
