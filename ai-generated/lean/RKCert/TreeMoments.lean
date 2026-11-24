module

public import RKCert.ScaledRootCuts
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Normalized tree profiles and their mixed monomial moments

Multiplying the elementary stage column by the product of the factorials of its
children gives the integral-free normalization with scalar profile `x^(|t|-1)`.
All moment identities in this file hold over arbitrary commutative semirings.
-/

namespace RKCert
namespace Paired

variable {R : Type*} [CommSemiring R] {s : ℕ}

abbrev Vec (R : Type*) (s : ℕ) := Fin s → R

/-- Applying a tableau as a linear operator on columns. -/
def mat (A : Fin s → Fin s → R) : Vec R s →ₗ[R] Vec R s :=
  Matrix.mulVecLin A

/-- Multiplication by a fixed stage column, coordinate by coordinate. -/
def diag (c : Vec R s) : Vec R s →ₗ[R] Vec R s :=
  LinearMap.mulLeft R c

/-- A row as a linear functional, without any nonzero-weight hypothesis. -/
def row (w : Vec R s) : Vec R s →ₗ[R] R :=
  dotProductEquiv R (Fin s) w

@[simp] theorem mat_apply (A : Fin s → Fin s → R) (v : Vec R s) (i : Fin s) :
    mat A v i = ∑ j, A i j * v j := rfl

@[simp] theorem diag_apply (c v : Vec R s) (i : Fin s) :
    diag c v i = c i * v i := rfl

@[simp] theorem row_apply (w v : Vec R s) : row w v = ∑ i, w i * v i := rfl

/-- Weighted monomial probes of a stage column. -/
def probe (A : Fin s → Fin s → R) (b : Vec R s) (k : ℕ) : Vec R s →ₗ[R] R :=
  row (fun i => b i * nodes A i ^ k)

/-- The normalized stage column; for genuine order its multiplier is a unit. -/
def normTree (A : Fin s → Fin s → R) (t : Tree) : Vec R s :=
  (t.childDensityProduct : R) • stageWeight A t

theorem normTree_leaf (A : Fin s → Fin s → R) : normTree A .leaf = 1 := by
  ext i; simp [normTree, Tree.childDensityProduct, stageWeight]

theorem normTree_bush (A : Fin s → Fin s → R) (k : ℕ) :
    normTree A (Tree.bush k) = (fun i => nodes A i ^ k) := by
  ext i
  simp only [normTree, Tree.bush, Tree.childDensityProduct_addLeaves,
    Tree.childDensityProduct, Nat.cast_one, one_smul, stageWeight_addLeaves, stageWeight, mul_one]

/-- Exact moment of every normalized tree, with its precise joint vertex budget. -/
theorem probe_normTree {A : Fin s → Fin s → R} {b : Vec R s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (t : Tree) (k : ℕ) (hk : k+t.order ≤ p) :
    ((k + t.order : ℕ) : R) * probe A b k (normTree A t) = 1 := by
  have h := ho (Tree.addLeaves k t) (by simpa only [Tree.order_addLeaves] using hk)
  rw [Tree.density_addLeaves, Nat.cast_mul, mul_assoc] at h
  convert h using 2
  simp only [probe, row_apply, normTree, Pi.smul_apply, smul_eq_mul, weight,
    stageWeight_addLeaves, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

theorem normTree_first (A : Fin (s+1) → Fin (s+1) → R) (ha : StrictLower A) (t : Tree) :
    normTree A t 0 = if t = .leaf then 1 else 0 := by
  cases t with
  | leaf => simp [normTree_leaf]
  | attach t u =>
    have hh (j : Fin (s+1)) : A 0 j = 0 := ha 0 j (Nat.zero_le _)
    simp [normTree, stageWeight, hh]

/-- The graded space of all actual stage columns of trees with at most `j+1` vertices. -/
def treeSpace (A : Fin s → Fin s → R) (j : ℕ) : Submodule R (Vec R s) :=
  Submodule.span R { v | ∃ t : Tree, t.order ≤ j+1 ∧ v = stageWeight A t }

theorem stageWeight_mem_space (A : Fin s → Fin s → R) (t : Tree) {j : ℕ}
    (ht : t.order ≤ j+1) : stageWeight A t ∈ treeSpace A j :=
  Submodule.subset_span ⟨t, ht, rfl⟩

theorem treeSpace_mono (A : Fin s → Fin s → R) {j k : ℕ} (hj : j ≤ k) :
    treeSpace A j ≤ treeSpace A k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  exact stageWeight_mem_space A t (by omega)

theorem mat_treeSpace (A : Fin s → Fin s → R) (j : ℕ) :
    treeSpace A j ≤ (treeSpace A (j+1)).comap (mat A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  change mat A (stageWeight A t) ∈ treeSpace A (j+1)
  have hh : mat A (stageWeight A t) = stageWeight A (.attach t .leaf) := by
    ext i; simp [stageWeight]
  rw [hh]
  exact stageWeight_mem_space A _ (by change t.order+1 ≤ j+1+1; omega)

theorem diag_treeSpace (A : Fin s → Fin s → R) (j : ℕ) :
    treeSpace A j ≤ (treeSpace A (j+1)).comap (diag (nodes A)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  change diag (nodes A) (stageWeight A t) ∈ treeSpace A (j+1)
  have hh : diag (nodes A) (stageWeight A t) = stageWeight A (.attach .leaf t) := by
    ext i; simp [stageWeight, nodes]
  rw [hh]
  exact stageWeight_mem_space A _ (by change 1+t.order ≤ j+1+1; omega)

end Paired
end RKCert
