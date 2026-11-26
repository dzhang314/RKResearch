module

public import RKCert.ReviewedNative.RationalDonorChain
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The first three sites in the actual first bank of the one-zero-seed
rational donor chain give the quiet contrast (1,-2,1). This is a statement
about those chronological rows, not terminal weights or tableau order. -/

namespace RKResearch.Certified.RationalFirstBankQuietGain

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation
open RKResearch.Certified.RationalDonorChain
open scoped FiniteRootedTree Matrix

abbrev Stages (d n : ℕ) := Fin (1 + (d + 1) * n)

abbrev twoNode : FiniteRootedTree := .leaf ◂ .leaf

private theorem twoNode_order : (twoNode.order : ℕ) = 2 := rfl
private theorem twoNode_forest : (twoNode.forestFactorial : ℕ) = 1 := rfl
private theorem twoNode_factorial : (twoNode.factorial : ℕ) = 2 := rfl

variable {ι : Type*} [Fintype ι]

private theorem phi_twoNode (A : Matrix ι ι ℚ) :
    Φ twoNode A = nodes A := by
  simp only [twoNode, Φ, one_mul, nodes]

private theorem normTree_twoNode (A : Matrix ι ι ℚ) :
    normTree A twoNode = nodes A := by
  simp only [normTree, twoNode_forest, Nat.cast_one, one_smul, phi_twoNode]

/-- The denominator-cleared Q([•]) is the literal column 2Ac-c²,
with c the row sum of this same matrix. -/
theorem twoNode_residual_formula (A : Matrix ι ι ℚ) (i : ι) :
    rootStageResidual A twoNode i =
      2 * (A *ᵥ nodes A) i - (nodes A i) ^ 2 := by
  change ((twoNode.factorial : ℕ) : ℚ) * (A *ᵥ Φ twoNode A) i -
      (nodes A i) ^ (twoNode.order : ℕ) = _
  norm_num only [phi_twoNode, twoNode_factorial, twoNode_order]

/-- The same actual column is the one consumed by the terminal core. -/
theorem twoNode_residual_eq_monomial (A : Matrix ι ι ℚ) :
    rootStageResidual A twoNode = monomialStageDefect A 1 := by
  funext i
  change rootStageResidual A twoNode i =
      ((1 + 1 : ℕ) : ℚ) * (A *ᵥ (nodes A)^1) i - (nodes A i)^(1 + 1)
  norm_num only [twoNode_residual_formula, pow_one]

private theorem quiet_of_two_moments (A : Matrix ι ι ℚ) (η : ι → ℚ)
    (mass : row η (1 : ι → ℚ) = 0) (clock : row η (nodes A) = 0) :
    Quiet A η 2 := by
  intro t paid
  cases t with
  | leaf =>
    simpa only [normTree_leaf] using mass
  | butcherProduct u v =>
    change ((u ◂ v).order : ℕ) ≤ 2 at paid
    simp only [FiniteRootedTree.order, PNat.add_coe] at paid
    have hu : 1 ≤ (u.order : ℕ) := u.order.pos
    have hv : 1 ≤ (v.order : ℕ) := v.order.pos
    have hule : (u.order : ℕ) ≤ 1 :=
      Nat.le_of_add_le_add_right ((Nat.add_le_add_left hv (u.order : ℕ)).trans paid)
    have hvle : (v.order : ℕ) ≤ 1 :=
      Nat.le_of_add_le_add_left ((Nat.add_le_add_right hu (v.order : ℕ)).trans paid)
    have eu : u = .leaf := (coe_order_eq_one_iff_leaf u).mp (le_antisymm hule hu)
    have ev : v = .leaf := (coe_order_eq_one_iff_leaf v).mp (le_antisymm hvle hv)
    subst u
    subst v
    change row η (normTree A twoNode) = 0
    simpa only [normTree_twoNode] using clock

private theorem reindex_mulVec_apply {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (M : Matrix I I ℚ) (v : J → ℚ) (i : I) :
    (Matrix.reindex e e M *ᵥ v) (e i) = (M *ᵥ (v ∘ e)) i := by
  change (M.submatrix e.symm e.symm *ᵥ v) (e i) = _
  simpa only [Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply] using
    congrFun (Matrix.submatrix_mulVec_equiv M v e.symm e.symm) (e i)

def seedIndex (d n : ℕ) : Stages d n :=
  chronology 1 d n (Sum.inl 0)

def firstBankIndex {n : ℕ} (d : ℕ) (j : Fin n) : Stages d n :=
  chronology 1 d n (Sum.inr ⟨0, j⟩)

@[simp] theorem seedIndex_val (d n : ℕ) : (seedIndex d n).val = 0 := rfl

@[simp] theorem firstBankIndex_val {n : ℕ} (d : ℕ) (j : Fin n) :
    (firstBankIndex d j).val = 1 + j.val := by
  change (chronology 1 d n (Sum.inr (⟨0, j⟩ : Bank d n))).val = _
  simp only [chronology_inr_val, Fin.val_zero, Nat.mul_zero, Nat.add_zero]

variable {n : ℕ}

private theorem seed_clock (d : ℕ) (z : Fin n → ℚ) :
    nodes (pureBankMatrix d z) (seedIndex d n) = 0 := by
  change (Matrix.reindex (chronology 1 d n) (chronology 1 d n)
      (chain (d := d) oneSeed (oneSeedRows z) z) *ᵥ
        (1 : Stages d n → ℚ)) (chronology 1 d n (Sum.inl 0)) = 0
  rw [reindex_mulVec_apply, chain_mulVec_inl, oneSeed, Matrix.zero_mulVec, Pi.zero_apply]

/-- An actual chronological Fin row of the first bank reads only the
unique zero-seed stage, with coefficient z j. -/
theorem firstBank_mulVec (d : ℕ) (z : Fin n → ℚ) (v : Stages d n → ℚ) (j : Fin n) :
    (pureBankMatrix d z *ᵥ v) (firstBankIndex d j) = z j * v (seedIndex d n) := by
  change (Matrix.reindex (chronology 1 d n) (chronology 1 d n)
      (chain (d := d) oneSeed (oneSeedRows z) z) *ᵥ v)
        (chronology 1 d n (Sum.inr (⟨0, j⟩ : Bank d n))) = _
  rw [reindex_mulVec_apply, chain_mulVec_first oneSeed (oneSeedRows z) z
    (v ∘ chronology 1 d n) (⟨0, j⟩ : Bank d n) rfl]
  simp only [row_apply, dotProduct, Fin.sum_univ_one, oneSeedRows, Function.comp_apply, seedIndex]

theorem firstBank_clock (d : ℕ) (z : Fin n → ℚ) (j : Fin n) :
    nodes (pureBankMatrix d z) (firstBankIndex d j) = z j := by
  change (pureBankMatrix d z *ᵥ (1 : Stages d n → ℚ)) (firstBankIndex d j) = _
  rw [firstBank_mulVec, Pi.one_apply, mul_one]

/-- The only local input to Ac is this actual seed clock, which is zero. -/
theorem firstBank_residual (d : ℕ) (z : Fin n → ℚ) (j : Fin n) :
    rootStageResidual (pureBankMatrix d z) twoNode (firstBankIndex d j) = -((z j)^2) := by
  have action : (pureBankMatrix d z *ᵥ nodes (pureBankMatrix d z))
      (firstBankIndex d j) = 0 := by
    rw [firstBank_mulVec, seed_clock, mul_zero]
  simp only [twoNode_residual_formula, action, mul_zero, firstBank_clock, zero_sub]

/-- The three physical sites are in bank zero at ranks 1, 2, and 3. -/
def contrastIndex (d : ℕ) (wide : 3 ≤ n) (j : Fin 3) : Stages d n :=
  firstBankIndex d (Fin.castLE wide j)

@[simp] theorem contrastIndex_val (d : ℕ) (wide : 3 ≤ n) (j : Fin 3) :
    (contrastIndex d wide j).val = 1 + j.val := by
  simp only [contrastIndex, firstBankIndex_val, Fin.val_castLE]

/-- Literal taps on the three chronological sites and zero outside them. -/
def contrast (d : ℕ) (wide : 3 ≤ n) : Stages d n → ℚ :=
  Pi.single (contrastIndex d wide 0) (1 : ℚ) +
    Pi.single (contrastIndex d wide 1) (-2 : ℚ) +
    Pi.single (contrastIndex d wide 2) (1 : ℚ)

theorem contrast_row (d : ℕ) (wide : 3 ≤ n) (v : Stages d n → ℚ) :
    row (contrast d wide) v =
      v (contrastIndex d wide 0) + (-2 : ℚ) * v (contrastIndex d wide 1) +
        v (contrastIndex d wide 2) := by
  simp only [contrast, row_apply, add_dotProduct, single_dotProduct, one_mul]

/-- For rational natural samples, the first-bank contrast kills every
actual normalized tree through order two and has exact gain -2 on
the denominator-cleared Q([•]), in both native presentations. -/
theorem contrast_quiet_gain (d : ℕ) (wide : 3 ≤ n) :
    let A := pureBankMatrix d (fun j : Fin n => (j.val : ℚ))
    Quiet A (contrast d wide) 2 ∧
      row (contrast d wide) (rootStageResidual A twoNode) = -2 ∧
      row (contrast d wide) (monomialStageDefect A 1) = -2 := by
  let z : Fin n → ℚ := fun j => j.val
  let A := pureBankMatrix d z
  change Quiet A (contrast d wide) 2 ∧
    row (contrast d wide) (rootStageResidual A twoNode) = -2 ∧
    row (contrast d wide) (monomialStageDefect A 1) = -2
  have hc (j : Fin 3) : nodes A (contrastIndex d wide j) = (j.val : ℚ) := by
    change nodes (pureBankMatrix d z) (firstBankIndex d (Fin.castLE wide j)) = _
    exact firstBank_clock d z (Fin.castLE wide j)
  have hq (j : Fin 3) :
      rootStageResidual A twoNode (contrastIndex d wide j) = -((j.val : ℚ)^2) := by
    change rootStageResidual (pureBankMatrix d z) twoNode
      (firstBankIndex d (Fin.castLE wide j)) = _
    exact firstBank_residual d z (Fin.castLE wide j)
  have mass : row (contrast d wide) (1 : Stages d n → ℚ) = 0 := by
    simp only [contrast_row, Pi.one_apply] <;> norm_num
  have clock : row (contrast d wide) (nodes A) = 0 := by
    simp only [contrast_row, hc] <;>
      change (0 : ℚ) + (-2) * 1 + 2 = 0 <;> norm_num
  have gain : row (contrast d wide) (rootStageResidual A twoNode) = -2 := by
    simp only [contrast_row, hq] <;>
      change -((0 : ℚ)^2) + (-2) * (-((1 : ℚ)^2)) + (-((2 : ℚ)^2)) = -2 <;> norm_num
  exact ⟨quiet_of_two_moments A (contrast d wide) mass clock, gain,
    by simpa only [twoNode_residual_eq_monomial] using gain⟩

end RKResearch.Certified.RationalFirstBankQuietGain
