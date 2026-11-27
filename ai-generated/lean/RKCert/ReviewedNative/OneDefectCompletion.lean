module

public import RKResearch.OrderConditions
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Turning one coupled integration defect into a completed prefix read

If the tail integrates a particular missing polynomial itself, moving
a genuine observation of that polynomial into the prefix has an exact
row-by-row algebraic interpretation. No extra stage is inserted.
-/

namespace RKResearch.Certified.OneDefectCompletion

open scoped BigOperators Matrix
variable {K κ ι : Type*} [Field K] [Fintype κ] [Fintype ι]

/-- A column response is unaffected by subtracting the component of the
missing mode specified by the paid observation. -/
theorem projection_response (M : Matrix ι κ K) (q z : κ → K) (α : K)
    (hq : M *ᵥ q = 0) :
    M *ᵥ (z - α • q) = M *ᵥ z := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hq, smul_zero, sub_zero]

/-- The very same row after its actual paid observation is treated as a
prefix value. The identity acts on arbitrary numerical stage columns,
not only the trees used to identify the missing direction. -/
theorem complete_feed (l e q z : κ → K) (β a : K) (hz : e ⬝ᵥ q ≠ 0)
    (hp : l ⬝ᵥ q = β*(e ⬝ᵥ q)) :
    l ⬝ᵥ (z + ((a-e ⬝ᵥ z)/(e ⬝ᵥ q)) • q) =
      (l-β • e) ⬝ᵥ z + β*a := by
  rw [dotProduct_add, dotProduct_smul, sub_dotProduct, smul_dotProduct, hp]
  simp only [smul_eq_mul]
  field_simp [hz]
  ring

/-- In a paid column identity, all later rows with zero values of the
missing mode are inert. A last live diagonal-one column therefore
forces the selected clock to be a root of the shifted primitive. -/
theorem last_paid_column [DecidableEq ι] (S : Matrix ι ι K)
    (w q integral : ι → K) (j : ι) (hw : w j ≠ 0)
    (hdiag : S j j = 1)
    (hcausal : ∀ i, i ≠ j → S i j = 0 ∨ q i = 0)
    (hpay : (∑ i, w i*q i*S i j) = w j*integral j) :
    integral j = q j := by
  have h : (∑ i, w i*q i*S i j) = w j*q j := by
    rw [Finset.sum_eq_single j]
    · rw [hdiag, mul_one]
    · intro i _ hij
      rcases hcausal i hij with hi|hi
      · rw [hi,mul_zero]
      · rw [hi,mul_zero,zero_mul]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  exact (mul_left_cancel₀ hw (h.symm.trans hpay)).symm

#print axioms projection_response
#print axioms complete_feed
#print axioms last_paid_column

end RKResearch.Certified.OneDefectCompletion
