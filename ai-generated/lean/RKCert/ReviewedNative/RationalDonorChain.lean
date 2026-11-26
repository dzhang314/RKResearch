module

public import RKCert.ReviewedNative.AdjacentLayerRows
public import RKCert.ReviewedNative.ERKTerminalDeformation
public import RKCert.ReviewedNative.RationalVandermondeMoments
public import Mathlib.Logic.Equiv.Fin.Basic
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Chronological rational donor banks, with literal normalized tree and
clock values. This module constructs donor rows, not terminal weights. -/

namespace RKResearch.Certified.RationalDonorChain

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation
open RKResearch.Certified.RationalMoments
open RKResearch.FiniteSeries.AdjacentLayerRows
open scoped BigOperators FiniteRootedTree Matrix

abbrev Bank (d n : ℕ) := Σ _ : Fin (d + 1), Fin n
abbrev Site (s d n : ℕ) := Fin s ⊕ Bank d n

variable {s d n : ℕ}

def seedTap (D₀ : Matrix (Fin n) (Fin s) ℚ) :
    Matrix (Bank d n) (Fin s) ℚ :=
  fun i j => if i.1.val = 0 then D₀ i.2 j else 0

noncomputable def rawBank (z : Fin n → ℚ) : Matrix (Bank d n) (Bank d n) ℚ :=
  fun i j => primitiveWeights z (z i.2) j.2

/-- Seed, then one actual zero-masked bank matrix. -/
noncomputable def chain (A₀ : Matrix (Fin s) (Fin s) ℚ)
    (D₀ : Matrix (Fin n) (Fin s) ℚ) (z : Fin n → ℚ) :
    Matrix (Site s d n) (Site s d n) ℚ :=
  Matrix.fromBlocks A₀ (0 : Matrix (Fin s) (Bank d n) ℚ)
    (seedTap (d := d) D₀) (adjacentMask (rawBank (d := d) z))

section Labeled

variable (A₀ : Matrix (Fin s) (Fin s) ℚ)
  (D₀ : Matrix (Fin n) (Fin s) ℚ) (z : Fin n → ℚ)

theorem chain_mulVec_inl (v : Site s d n → ℚ) (i : Fin s) :
    (chain (d := d) A₀ D₀ z *ᵥ v) (Sum.inl i) = (A₀ *ᵥ (v ∘ Sum.inl)) i := by
  simp [chain, Matrix.fromBlocks_mulVec]

private theorem chain_mulVec_inr (v : Site s d n → ℚ) (i : Bank d n) :
    (chain (d := d) A₀ D₀ z *ᵥ v) (Sum.inr i) =
      (seedTap (d := d) D₀ *ᵥ (v ∘ Sum.inl)) i +
      (adjacentMask (rawBank (d := d) z) *ᵥ (v ∘ Sum.inr)) i := by
  simp only [chain, Matrix.fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply]

theorem chain_mulVec_first (v : Site s d n → ℚ) (i : Bank d n)
    (first : i.1.val = 0) :
    (chain (d := d) A₀ D₀ z *ᵥ v) (Sum.inr i) = row (D₀ i.2) (v ∘ Sum.inl) := by
  have hzero : (adjacentMask (rawBank (d := d) z) *ᵥ (v ∘ Sum.inr)) i = 0 :=
    mulVec_adjacentMask_eq_zero_first (rawBank (d := d) z) (v ∘ Sum.inr) i first
  rw [chain_mulVec_inr, hzero, add_zero, row_apply]
  have hs : seedTap (d := d) D₀ i = D₀ i.2 := by
    funext j
    simp only [seedTap, if_pos first]
  change seedTap (d := d) D₀ i ⬝ᵥ (v ∘ Sum.inl) = _
  rw [hs]

theorem chain_mulVec_parent (v : Site s d n → ℚ) (i : Bank d n)
    (k : Fin (d + 1)) (parent : k.val + 1 = i.1.val) :
    (chain (d := d) A₀ D₀ z *ᵥ v) (Sum.inr i) =
      ∑ j : Fin n, primitiveWeights z (z i.2) j * v (Sum.inr ⟨k, j⟩) := by
  have later : i.1.val ≠ 0 := by omega
  have hs : seedTap (d := d) D₀ i = 0 := by
    funext j
    simp only [seedTap, if_neg later, Pi.zero_apply]
  have hz : (seedTap (d := d) D₀ *ᵥ (v ∘ Sum.inl)) i = 0 := by
    change seedTap (d := d) D₀ i ⬝ᵥ (v ∘ Sum.inl) = 0
    rw [hs, zero_dotProduct]
  rw [chain_mulVec_inr, hz, zero_add]
  simpa only [layerSlice, rawBank, dotProduct, Function.comp_apply] using
    (mulVec_adjacentMask_eq_on_parent (rawBank (d := d) z) (v ∘ Sum.inr) i k parent)

theorem phi_chain_inl (t : FiniteRootedTree) :
    Φ t (chain (d := d) A₀ D₀ z) ∘ Sum.inl = Φ t A₀ := by
  induction t with
  | leaf => rfl
  | butcherProduct u v ihu ihv =>
    funext i
    have hu : Φ u (chain (d := d) A₀ D₀ z) (Sum.inl i) = Φ u A₀ i := congrFun ihu i
    change Φ u (chain (d := d) A₀ D₀ z) (Sum.inl i) *
      (chain (d := d) A₀ D₀ z *ᵥ Φ v (chain (d := d) A₀ D₀ z)) (Sum.inl i) =
      Φ u A₀ i * (A₀ *ᵥ Φ v A₀) i
    rw [hu, chain_mulVec_inl, ihv]

theorem normTree_chain_inl (t : FiniteRootedTree) :
    normTree (chain (d := d) A₀ D₀ z) t ∘ Sum.inl = normTree A₀ t := by
  funext i
  have h : Φ t (chain (d := d) A₀ D₀ z) (Sum.inl i) = Φ t A₀ i :=
    congrFun (phi_chain_inl (d := d) A₀ D₀ z t) i
  simp only [Function.comp_apply, normTree, Pi.smul_apply, h]

end Labeled

private theorem primitive_payment {z : Fin n → ℚ} (inj : Function.Injective z)
    (x : ℚ) (m : ℕ) (pos : 0 < m) (cap : m ≤ n) :
    (m : ℚ) * (∑ j, primitiveWeights z x j * z j ^ (m - 1)) = x ^ m := by
  let k : Fin n := ⟨m - 1, by omega⟩
  have hk : k.val + 1 = m := by
    dsimp only [k]
    omega
  have nz : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt pos)
  change (m : ℚ) * (∑ j, primitiveWeights z x j * z j ^ k.val) = _
  rw [primitiveWeights_spec inj x k, hk, mul_comm (m : ℚ), div_mul_cancel₀ _ nz]

/-- The first bank is paid by the actual seed RowLaw. Every higher bank
pays one more tree order because the branch reads its true predecessor. -/
theorem chain_pure {r₀ : ℕ} {A₀ : Matrix (Fin s) (Fin s) ℚ}
    {D₀ : Matrix (Fin n) (Fin s) ℚ} {z : Fin n → ℚ}
    (inj : Function.Injective z) (base : RowLaw A₀ D₀ z r₀) (cap : r₀ + d ≤ n + 1)
    (i : Bank d n) (t : FiniteRootedTree) (paid : ord t ≤ r₀ + i.1.val) :
    normTree (chain (d := d) A₀ D₀ z) t (Sum.inr i) = z i.2 ^ (ord t - 1) := by
  revert i
  induction t with
  | leaf =>
    intro i _
    simp [ord]
  | butcherProduct u v ihu ihv =>
    intro i paid
    let M := chain (d := d) A₀ D₀ z
    have hu : 0 < ord u := u.order.pos
    have hv : 0 < ord v := v.order.pos
    have ht : ord (u ◂ v) = ord u + ord v := by
      simp only [ord, FiniteRootedTree.order, PNat.add_coe]
    have up : ord u ≤ r₀ + i.1.val := by omega
    have hexp : ord u - 1 + ord v = ord (u ◂ v) - 1 := by omega
    have hbase : normTree M u (Sum.inr i) = z i.2 ^ (ord u - 1) := ihu i up
    have action : (ord v : ℚ) * (M *ᵥ normTree M v) (Sum.inr i) = z i.2 ^ ord v := by
      by_cases first : i.1.val = 0
      · have hrow : (M *ᵥ normTree M v) (Sum.inr i) =
            row (D₀ i.2) (normTree M v ∘ Sum.inl) :=
          chain_mulVec_first A₀ D₀ z (normTree M v) i first
        have hseed : normTree M v ∘ Sum.inl = normTree A₀ v :=
          normTree_chain_inl (d := d) A₀ D₀ z v
        rw [hrow, hseed]
        exact base i.2 v (by omega)
      · have hi : i.1.val < d + 1 := i.1.isLt
        let k : Fin (d + 1) := ⟨i.1.val - 1, by omega⟩
        have parent : k.val + 1 = i.1.val := by
          dsimp only [k]
          omega
        have vp : ord v ≤ r₀ + k.val := by omega
        have vn : ord v ≤ n := by omega
        have hbank (j : Fin n) :
            normTree M v (Sum.inr (⟨k, j⟩ : Bank d n)) = z j ^ (ord v - 1) :=
          ihv ⟨k, j⟩ vp
        have hrow : (M *ᵥ normTree M v) (Sum.inr i) =
            ∑ j : Fin n, primitiveWeights z (z i.2) j *
              normTree M v (Sum.inr (⟨k, j⟩ : Bank d n)) :=
          chain_mulVec_parent A₀ D₀ z (normTree M v) i k parent
        rw [hrow]
        simp_rw [hbank]
        exact primitive_payment inj (z i.2) (ord v) hv vn
    change normTree M (u ◂ v) (Sum.inr i) = _
    rw [normTree_graft, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hbase, mat_apply,
      action, ← pow_add, hexp]

/-- Canonical physical indexing, with the whole seed prefix first. -/
def chronology (s d n : ℕ) : Site s d n ≃ Fin (s + (d + 1) * n) :=
  (Equiv.sumCongr (Equiv.refl (Fin s))
    ((Equiv.sigmaEquivProd (Fin (d + 1)) (Fin n)).trans finProdFinEquiv)).trans
      finSumFinEquiv

@[simp] theorem chronology_inl_val (i : Fin s) :
    (chronology s d n (Sum.inl i)).val = i.val := rfl

@[simp] theorem chronology_inr_val (i : Bank d n) :
    (chronology s d n (Sum.inr i)).val = s + (i.2.val + n * i.1.val) := rfl

noncomputable def chainFin (A₀ : Matrix (Fin s) (Fin s) ℚ)
    (D₀ : Matrix (Fin n) (Fin s) ℚ) (z : Fin n → ℚ) :
    Matrix (Fin (s + (d + 1) * n)) (Fin (s + (d + 1) * n)) ℚ :=
  Matrix.reindex (chronology s d n) (chronology s d n) (chain (d := d) A₀ D₀ z)

private theorem edge_chronological {A₀ : Matrix (Fin s) (Fin s) ℚ}
    (strict₀ : ∀ i j, i ≤ j → A₀ i j = 0)
    (D₀ : Matrix (Fin n) (Fin s) ℚ) (z : Fin n → ℚ) (i j : Site s d n)
    (edge : chain (d := d) A₀ D₀ z i j ≠ 0) :
    chronology s d n j < chronology s d n i := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have nz : A₀ i j ≠ 0 := by simpa only [chain, Matrix.fromBlocks_apply₁₁] using edge
      have lt : j < i := lt_of_not_ge (fun le => nz (strict₀ i j le))
      change (chronology s d n (Sum.inl j)).val < (chronology s d n (Sum.inl i)).val
      simpa only [chronology_inl_val] using (show j.val < i.val from lt)
    | inr j =>
      have hz : chain (d := d) A₀ D₀ z (Sum.inl i) (Sum.inr j) = 0 := rfl
      exact (edge hz).elim
  | inr i =>
    cases j with
    | inl j =>
      change (chronology s d n (Sum.inl j)).val < (chronology s d n (Sum.inr i)).val
      simp only [chronology_inl_val, chronology_inr_val]
      have hj : j.val < s := j.isLt
      omega
    | inr j =>
      have parent : j.1.val + 1 = i.1.val := by
        apply Classical.byContradiction
        intro off
        apply edge
        simpa only [chain, Matrix.fromBlocks_apply₂₂] using
          (adjacentMask_off (rawBank (d := d) z) i j off)
      have hj : j.2.val < n := j.2.isLt
      have hmul : n * j.1.val + n = n * i.1.val := by
        calc
          _ = n * (j.1.val + 1) := by
            simpa only [Nat.succ_eq_add_one] using (Nat.mul_succ n j.1.val).symm
          _ = _ := congrArg (fun k : ℕ => n * k) parent
      change (chronology s d n (Sum.inr j)).val < (chronology s d n (Sum.inr i)).val
      simp only [chronology_inr_val]
      omega

/-- Literal strict lower triangularity, including the physical diagonal. -/
theorem chainFin_strict {A₀ : Matrix (Fin s) (Fin s) ℚ}
    (strict₀ : ∀ i j, i ≤ j → A₀ i j = 0)
    (D₀ : Matrix (Fin n) (Fin s) ℚ) (z : Fin n → ℚ)
    (i j : Fin (s + (d + 1) * n)) (le : i ≤ j) :
    chainFin (d := d) A₀ D₀ z i j = 0 := by
  apply Classical.byContradiction
  intro nz
  let e := chronology s d n
  have edge : chain (d := d) A₀ D₀ z (e.symm i) (e.symm j) ≠ 0 := by
    simpa only [chainFin, Matrix.reindex_apply, Matrix.submatrix_apply, e] using nz
  have hj : e (e.symm j) < e (e.symm i) := edge_chronological strict₀ D₀ z _ _ edge
  exact (not_lt_of_ge le) (by simpa only [Equiv.apply_symm_apply] using hj)

private theorem reindex_mulVec {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (A : Matrix I I ℚ) (v : I → ℚ) :
    Matrix.reindex e e A *ᵥ (v ∘ e.symm) = (A *ᵥ v) ∘ e.symm := by
  have back : (v ∘ e.symm) ∘ e.symm.symm = v := by
    funext i
    simp only [Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  change A.submatrix e.symm e.symm *ᵥ (v ∘ e.symm) = _
  rw [Matrix.submatrix_mulVec_equiv A (v ∘ e.symm) e.symm e.symm, back]

private theorem reindex_phi {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (A : Matrix I I ℚ) (t : FiniteRootedTree) :
    Φ t (Matrix.reindex e e A) = Φ t A ∘ e.symm := by
  induction t with
  | leaf => rfl
  | butcherProduct u v ihu ihv =>
    funext i
    have hu : Φ u (Matrix.reindex e e A) i = Φ u A (e.symm i) := congrFun ihu i
    change Φ u (Matrix.reindex e e A) i *
      (Matrix.reindex e e A *ᵥ Φ v (Matrix.reindex e e A)) i =
      Φ u A (e.symm i) * (A *ᵥ Φ v A) (e.symm i)
    rw [hu, ihv, reindex_mulVec, Function.comp_apply]

private theorem reindex_norm_apply {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (A : Matrix I I ℚ) (t : FiniteRootedTree) (i : I) :
    normTree (Matrix.reindex e e A) t (e i) = normTree A t i := by
  have h : Φ t (Matrix.reindex e e A) (e i) = Φ t A i := by
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
      congrFun (reindex_phi e A t) (e i)
  simp only [normTree, Pi.smul_apply, h]

/-- Purity on the indexed physical tableau, not just on an abstract bank. -/
theorem chainFin_pure {r₀ : ℕ} {A₀ : Matrix (Fin s) (Fin s) ℚ}
    {D₀ : Matrix (Fin n) (Fin s) ℚ} {z : Fin n → ℚ}
    (inj : Function.Injective z) (base : RowLaw A₀ D₀ z r₀) (cap : r₀ + d ≤ n + 1)
    (i : Bank d n) (t : FiniteRootedTree) (paid : ord t ≤ r₀ + i.1.val) :
    normTree (chainFin (d := d) A₀ D₀ z) t (chronology s d n (Sum.inr i)) =
      z i.2 ^ (ord t - 1) :=
  (reindex_norm_apply (chronology s d n) (chain (d := d) A₀ D₀ z) t (Sum.inr i)).trans
    (chain_pure (d := d) inj base cap i t paid)

theorem chainFin_clock {r₀ : ℕ} {A₀ : Matrix (Fin s) (Fin s) ℚ}
    {D₀ : Matrix (Fin n) (Fin s) ℚ} {z : Fin n → ℚ}
    (inj : Function.Injective z) (base : RowLaw A₀ D₀ z r₀) (cap : r₀ + d ≤ n + 1)
    (h₂ : 2 ≤ r₀) (i : Bank d n) :
    nodes (chainFin (d := d) A₀ D₀ z) (chronology s d n (Sum.inr i)) = z i.2 := by
  have ht : ord (clockTree 1) = 2 := order_clockTree 1
  have paid : ord (clockTree 1) ≤ r₀ + i.1.val := by rw [ht]; omega
  have exp : (2 : ℕ) - 1 = 1 := rfl
  simpa only [normTree_clockTree, ht, exp, pow_one] using
    (chainFin_pure (d := d) inj base cap i (clockTree 1) paid)

def oneSeed : Matrix (Fin 1) (Fin 1) ℚ := 0

def oneSeedRows (z : Fin n → ℚ) : Matrix (Fin n) (Fin 1) ℚ := fun x _ => z x

theorem oneSeed_rowLaw (z : Fin n → ℚ) : RowLaw oneSeed (oneSeedRows z) z 2 := by
  intro x t pay
  have positive : 0 < ord t := t.order.pos
  have ho : ord t = 1 := by omega
  have hleaf : t = .leaf := (coe_order_eq_one_iff_leaf t).mp ho
  subst t
  simp [ord, oneSeedRows, row_apply, dotProduct, Fin.sum_univ_one]

/-- A concrete seed and pure final donor bank, independently of any
terminal weights or eventual full order claim. -/
noncomputable def pureBankMatrix (d : ℕ) (z : Fin n → ℚ) :
    Matrix (Fin (1 + (d + 1) * n)) (Fin (1 + (d + 1) * n)) ℚ :=
  chainFin (d := d) oneSeed (oneSeedRows z) z

theorem pureBankMatrix_strict (d : ℕ) (z : Fin n → ℚ)
    (i j : Fin (1 + (d + 1) * n)) (le : i ≤ j) :
    pureBankMatrix d z i j = 0 :=
  chainFin_strict (d := d) (A₀ := oneSeed) (fun _ _ _ => rfl) (oneSeedRows z) z i j le

theorem pureBankMatrix_last (d : ℕ) {z : Fin n → ℚ} (inj : Function.Injective z)
    (cap : 2 + d ≤ n + 1) (x : Fin n) (t : FiniteRootedTree) (paid : ord t ≤ 2 + d) :
    normTree (pureBankMatrix d z) t (chronology 1 d n (Sum.inr ⟨Fin.last d, x⟩)) =
      z x ^ (ord t - 1) :=
  chainFin_pure (d := d) inj (oneSeed_rowLaw z) cap ⟨Fin.last d, x⟩ t paid

end RKResearch.Certified.RationalDonorChain
