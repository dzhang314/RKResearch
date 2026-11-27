module

public import RKCert.ReviewedNative.PaidDefectBridge
public import RKCert.ReviewedNative.DiagonalTwin

import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK149SevenClockPayments

open RKResearch FiniteRootedTree
open RKResearch.Certified.Graded (row mergeCoefficient)
open RKResearch.Certified.PaidDefectBridge
open RKResearch.Certified.DiagonalTwin
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

abbrev Paid (A : Matrix (Fin 9 ⊕ Fin 8) (Fin 9 ⊕ Fin 8) K)
    (w x : Fin 8 → K) (t : FiniteRootedTree) (W : List Letter) : Prop :=
  row w (wordMap (suffixBlock A) x W (primitiveSeed A x t)) = 0

/-- All actual order-nine rooted conditions from the seven eligible
word shapes when the prefix is exact through size five. -/
theorem orderNine_of_sevenPayments
    (A : Matrix (Fin 9 ⊕ Fin 8) (Fin 9 ⊕ Fin 8) K) (w x : Fin 8 → K)
    (hq : HasQuadratureOrder 9 w x)
    (h0 : ∀ t, treeSize t ≤ 5 → primitiveSeed A x t = 0)
    (hN : ∀ t, 5 < treeSize t → treeSize t ≤ 8 → Paid A w x t [])
    (hT : ∀ t, 5 < treeSize t → treeSize t ≤ 7 → Paid A w x t [.transport])
    (hC : ∀ t, 5 < treeSize t → treeSize t ≤ 7 → Paid A w x t [.clock])
    (hTT : ∀ t, treeSize t = 6 → Paid A w x t [.transport,.transport])
    (hTC : ∀ t, treeSize t = 6 → Paid A w x t [.transport,.clock])
    (hCT : ∀ t, treeSize t = 6 → Paid A w x t [.clock,.transport])
    (hCC : ∀ t, treeSize t = 6 → Paid A w x t [.clock,.clock]) :
    HasOrder 9 A (Sum.elim (0 : Fin 9 → K) w) := by
  refine hasOrder_of_paid_defect_words (p := 9) (q := 5) A w x
    (by decide) hq (fun t ht _ => h0 t ht) ?_
  intro t W ht hW
  cases W with
  | nil =>
    exact hN t ht (by simp at hW; omega)
  | cons a W =>
    cases W with
    | nil =>
      have h' : treeSize t ≤ 7 := by simp at hW; omega
      cases a with
      | transport => exact hT t ht h'
      | clock => exact hC t ht h'
    | cons b W =>
      have h' : treeSize t = 6 := by simp at hW; omega
      cases W with
      | nil =>
        cases a <;> cases b
        · exact hTT t h'
        · exact hTC t h'
        · exact hCT t h'
        · exact hCC t h'
      | cons c W =>
        simp at hW
        omega

/-- Contract the three literal staged readouts in chronology:
from the first high slot (index nine), into old stage 0,
then old stage 7, then old stage 8. Every equation in each
of the successive matrices is an ordinary reviewed order equation. -/
theorem contractOriginAndPorts
    (A : Matrix (Fin 17) (Fin 17) K) (b : Fin 17 → K)
    (hlo : A.IsLowerTriangular) (hdiag : ∀ i, A i i = 0)
    (ho : HasOrder 9 A b)
    (h₀ : DiagonalTwins (9 : Fin 17) (0 : Fin 16) 0 A)
    (h₁ : DiagonalTwins (9 : Fin 16) (7 : Fin 15) 0 (contractMatrix 9 0 A))
    (h₂ : DiagonalTwins (9 : Fin 15) (8 : Fin 14) 0
            (contractMatrix 9 7 (contractMatrix 9 0 A))) :
    let B := contractMatrix (9 : Fin 15) (8 : Fin 14)
      (contractMatrix (9 : Fin 16) (7 : Fin 15) (contractMatrix (9 : Fin 17) (0 : Fin 16) A))
    let v := mergeCoefficient (9 : Fin 15) (8 : Fin 14)
      (mergeCoefficient (9 : Fin 16) (7 : Fin 15) (mergeCoefficient (9 : Fin 17) (0 : Fin 16) b))
    B.IsLowerTriangular ∧ (∀ i, B i i = 0) ∧ HasOrder 9 B v := by
  let A0 := contractMatrix (9 : Fin 17) (0 : Fin 16) A
  let A1 := contractMatrix (9 : Fin 16) (7 : Fin 15) A0
  let b0 := mergeCoefficient (9 : Fin 17) (0 : Fin 16) b
  let b1 := mergeCoefficient (9 : Fin 16) (7 : Fin 15) b0
  have c0 : (9 : Fin 17).succAbove (0 : Fin 16) < 9 := by decide
  have c1 : (9 : Fin 16).succAbove (7 : Fin 15) < 9 := by decide
  have c2 : (9 : Fin 15).succAbove (8 : Fin 14) < 9 := by decide
  have lo0 : A0.IsLowerTriangular := contract_lower 9 0 A c0 hlo
  have lo1 : A1.IsLowerTriangular := contract_lower 9 7 A0 c1 lo0
  have d0 : ∀ i, A0 i i = 0 := fun i =>
    (contract_diagonal 9 0 A c0 hlo i).trans (hdiag _)
  have d1 : ∀ i, A1 i i = 0 := fun i =>
    (contract_diagonal 9 7 A0 c1 lo0 i).trans (d0 _)
  have o0 : HasOrder 9 A0 b0 := (hasOrder_contract_iff 9 0 A
    (rowsBalanced_of_diagonalTwins h₀) b).mpr ho
  have o1 : HasOrder 9 A1 b1 := (hasOrder_contract_iff 9 7 A0
    (rowsBalanced_of_diagonalTwins h₁) b0).mpr o0
  exact ⟨contract_lower 9 8 A1 c2 lo1,
    fun i => (contract_diagonal 9 8 A1 c2 lo1 i).trans (d1 _),
    (hasOrder_contract_iff 9 8 A1 (rowsBalanced_of_diagonalTwins h₂) b1).mpr o1⟩

end RKResearch.Certified.ERK149SevenClockPayments
