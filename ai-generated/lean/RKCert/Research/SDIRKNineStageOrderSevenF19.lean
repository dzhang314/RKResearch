module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # A nine-stage strict SDIRK tableau of exact order seven over F19

The matrix and output are literal integers in the prime field. The
native reviewed tree evaluator checks every rooted condition up to
order seven, and the eighth-order bush has factorial-scaled value 12.
-/
namespace RKResearch.Certified.SDIRKNineStageOrderSevenF19

open FiniteRootedTree
open scoped Matrix

abbrev F := ZMod 19

def A : Matrix (Fin 9) (Fin 9) F :=
  !![8,0,0,0,0,0,0,0,0;
     17,8,0,0,0,0,0,0,0;
     4,7,8,0,0,0,0,0,0;
     5,10,17,8,0,0,0,0,0;
     8,2,9,14,8,0,0,0,0;
     6,0,1,14,18,8,0,0,0;
     14,17,1,6,14,7,8,0,0;
     12,11,3,6,4,7,17,8,0;
     1,17,2,5,0,6,15,15,8]

def b : Fin 9→F := ![0,0,0,3,13,15,3,13,11]
def c : Fin 9→F := ![8,6,0,2,3,9,10,11,12]

theorem lowerTriangular : A.IsLowerTriangular := by
  intro i j h
  change i.val<j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(8:F) := by decide +kernel

theorem row_sums : A *ᵥ 1 = c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 9,(A *ᵥ 1) i = c i) i

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

theorem eighth_bush_value :
    ((bushyTree 8).factorial : F) * (b ⬝ᵥ Φ (bushyTree 8) A) = 12 := by
  rw [factorial_bushyTree,Φ_bushyTree,row_sums]
  decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h (bushyTree 8) (by rw [order_bushyTree]; decide)
  rw [eighth_bush_value] at e
  exact (by decide +kernel : (12:F)≠1) e

/-- The existence theorem has no hypothesis on any search chart or
weight mask. The lower endpoint is a separate exclusion result. -/
theorem exists_exact :
    ∃ (M : Matrix (Fin 9) (Fin 9) F) (w : Fin 9→F) (γ : F),
      M.IsLowerTriangular ∧ (∀ i, M i i=γ) ∧ IsUnit γ ∧
        HasOrder 7 M w ∧ ¬HasOrder 8 M w := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  refine ⟨A,b,8,lowerTriangular,diagonal,?_,order_seven,not_order_eight⟩
  exact (isUnit_iff_ne_zero).mpr (by decide +kernel)

end RKResearch.Certified.SDIRKNineStageOrderSevenF19
