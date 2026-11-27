module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKCert.ReviewedNative.GradedProducts
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Genuine cubic dirt at nine strict stages over F19

The first three weights vanish; the six remaining clocks and weights
are distinct and nonzero as needed. The third quadratic seed is zero,
but the actual cubic defect is visible on the first active stage.
This witness is independent of assumptions used in its finite search. -/
namespace RKResearch.Certified.SDIRKSevenSixActiveDirtyF19

open RKResearch Graded FiniteRootedTree
open scoped Matrix

abbrev K := ZMod 19

def A : Matrix (Fin 9) (Fin 9) K :=
  !![12,0,0,0,0,0,0,0,0;
     6,12,0,0,0,0,0,0,0;
     17,7,12,0,0,0,0,0,0;
     1,2,11,12,0,0,0,0,0;
     7,17,16,16,12,0,0,0,0;
     9,9,17,14,8,12,0,0,0;
     18,7,18,3,11,17,12,0,0;
     6,7,14,5,14,0,0,12,0;
     9,1,15,11,13,7,10,6,12]

def b : Fin 9→K := ![0,0,0,7,16,17,1,2,15]
def c : Fin 9→K := ![12,18,17,7,11,12,10,1,8]

theorem lowerTriangular : A.IsLowerTriangular := by
  intro i j h
  change i.val<j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(12:K) := by decide +kernel

theorem row_sums : A *ᵥ 1 = c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 9,(A *ᵥ 1) i = c i) i

theorem mask : (∀ i : Fin 9, i.val < 3 → b i=0) ∧ (∀ i : Fin 9,(3 : Nat) ≤ i.val → b i≠0) := by
  decide +kernel

theorem clocks : ∀ i j : Fin 9, (3 : Nat) ≤ i.val → (3 : Nat) ≤ j.val → c i=c j → i=j := by decide +kernel

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

theorem eighth_bush_value :
    ((bushyTree 8).factorial : K) * (b ⬝ᵥ Φ (bushyTree 8) A) = 6 := by
  rw [factorial_bushyTree,Φ_bushyTree,row_sums]
  decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h (bushyTree 8) (by rw [order_bushyTree]; decide)
  rw [eighth_bush_value] at e
  exact (by decide +kernel : (6:K)≠1) e

theorem third_seed_zero : monomialStageDefect A 1 2=0 := by
  -- This reduction only evaluates the literal nine-stage matrix.
  decide +kernel

theorem visible_cubic_defect :
    mat A (monomialStageDefect A 1)∈zeroSpace A 3 ∧
    mat A (monomialStageDefect A 1) 3=2 := by
  refine ⟨mat_zeroSpace order_seven 2 (by decide) (monomialStageDefect_mem A 1),?_⟩
  decide +kernel

theorem unpaid_third : Pi.single (2:Fin 9) (1:K)∉zeroSpace A 4 := by
  intro he
  have p := LinearMap.mem_ker.mp (probe_zeroSpace order_seven (k:=1) (by decide)
    (mat_zeroSpace order_seven 4 (by decide) he))
  have n : probe A b 1 (mat A (Pi.single (2:Fin 9) (1:K)))≠0 := by decide +kernel
  exact n p

/-- No uniform all-characteristic elimination of the unpaid chart can
hold: this strict tableau has a nonzero cubic defect on an active site. -/
theorem exists_dirty_exact :
    ∃ (M : Matrix (Fin 9) (Fin 9) K) (w : Fin 9→K) (γ : K),
      M.IsLowerTriangular ∧ (∀ i,M i i=γ) ∧ IsUnit γ ∧ HasOrder 7 M w ∧ ¬HasOrder 8 M w ∧
      (∀ i : Fin 9, i.val < 3 → w i=0) ∧ (∀ i : Fin 9, (3 : Nat) ≤ i.val → w i≠0) ∧
      (∀ i j : Fin 9, (3 : Nat) ≤ i.val → (3 : Nat) ≤ j.val → nodes M i=nodes M j → i=j) ∧
      monomialStageDefect M 1 2=0 ∧ Pi.single (2:Fin 9) (1:K)∉zeroSpace M 4 ∧
      ∃ v∈zeroSpace M 3, v 3≠0 := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  refine ⟨A,b,12,lowerTriangular,diagonal,isUnit_iff_ne_zero.mpr (by decide +kernel),
    order_seven,not_order_eight,mask.1,mask.2,?_,third_seed_zero,unpaid_third,
    mat A (monomialStageDefect A 1),visible_cubic_defect.1,?_⟩
  · show ∀ i j : Fin 9, (3 : Nat) ≤ i.val → (3 : Nat) ≤ j.val → (A *ᵥ 1) i=(A *ᵥ 1) j → i=j
    rw [row_sums]
    exact clocks
  · rw [visible_cubic_defect.2]
    decide +kernel

end RKResearch.Certified.SDIRKSevenSixActiveDirtyF19
