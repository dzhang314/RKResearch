module

public import RKCert.ReviewedNative.BushyMoments
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-! # Actual graded columns on the reviewed rooted trees

This module works directly with `FiniteRootedTree`, `Φ`, and `HasOrder`.
It imports no old tree representation or order-bridge theorem.
-/
namespace RKResearch.Certified.Graded

open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Raw tableau node: apply the native matrix to the constant-one column. -/
abbrev nodes (A : Matrix ι ι R) : ι → R := A *ᵥ 1

/-- Tableau, clock, and output row as Mathlib linear maps. -/
abbrev mat (A : Matrix ι ι R) : (ι → R) →ₗ[R] (ι → R) := Matrix.mulVecLin A
abbrev diag (c : ι → R) : (ι → R) →ₗ[R] (ι → R) := LinearMap.mulLeft R c
abbrev row (w : ι → R) : (ι → R) →ₗ[R] R := dotProductBilin R R w

theorem mat_apply (A : Matrix ι ι R) (v : ι → R) : mat A v = A *ᵥ v := rfl
omit [Fintype ι] in
@[simp] theorem diag_apply (c v : ι → R) (i : ι) : diag c v i = c i * v i := rfl
theorem row_apply (w v : ι → R) : row w v = w ⬝ᵥ v := rfl

/-- The weighted clock probe derived from the actual output row. -/
abbrev probe (A : Matrix ι ι R) (b : ι → R) (k : ℕ) : (ι → R) →ₗ[R] R :=
  row (fun i => b i * (nodes A i)^k)

/-- The native forest factorial scales out the internal tree factors. -/
def normTree (A : Matrix ι ι R) (t : FiniteRootedTree) : ι → R :=
  ((t.forestFactorial : ℕ) : R) • Φ t A

@[simp] theorem normTree_leaf (A : Matrix ι ι R) : normTree A .leaf = 1 := by
  simp [normTree]

theorem normTree_clock (A : Matrix ι ι R) (t : FiniteRootedTree) :
    normTree A (t ◂ .leaf) = diag (nodes A) (normTree A t) := by
  ext i
  simp only [normTree,forestFactorial,order,mul_one,Φ,diag_apply,
    Pi.smul_apply,smul_eq_mul,Pi.mul_apply,nodes]
  ac_rfl

theorem normTree_unary (A : Matrix ι ι R) (t : FiniteRootedTree) :
    normTree A (.leaf ◂ t) = ((t.order : ℕ) : R) • mat A (normTree A t) := by
  ext i
  simp only [normTree,forestFactorial,one_mul,PNat.mul_coe,Nat.cast_mul,Φ,
    Pi.smul_apply,smul_eq_mul,mat_apply,Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem normTree_appendLeafBranches (A : Matrix ι ι R) (k : ℕ) (t : FiniteRootedTree) :
    normTree A (appendLeafBranches k t) = fun i => (nodes A i)^k * normTree A t i := by
  rw [normTree,forestFactorial_appendLeafBranches,Φ_appendLeafBranches]
  ext i
  simp only [normTree,Pi.smul_apply,Pi.mul_apply,Pi.pow_apply,smul_eq_mul,nodes]
  ac_rfl

/-- The order-(n+1) reviewed bush corresponding to the clock monomial X^n. -/
abbrev clockTree (n : ℕ) : FiniteRootedTree := bushyTree n.succPNat

@[simp] theorem order_clockTree (n : ℕ) : ((clockTree n).order:ℕ)=n+1 := by
  simp [Nat.succ_eq_add_one]

theorem normTree_clockTree (A : Matrix ι ι R) (k : ℕ) :
    normTree A (clockTree k) = fun i => (nodes A i)^k := by
  rw [normTree,clockTree,forestFactorial_bushyTree,Φ_bushyTree]
  ext i
  simp [nodes,Nat.succ_eq_add_one]

/-- The denominator-cleared normalized probe identity at the exact grade
budget; no divisions, ordering, or cancellation are assumed. -/
theorem probe_normTree {A : Matrix ι ι R} {b : ι → R} {p : ℕ}
    (ho : HasOrder A b p) (t : FiniteRootedTree) (k : ℕ) (hk : k+(t.order:ℕ)≤p) :
    ((k+(t.order:ℕ):ℕ):R) * probe A b k (normTree A t) = 1 := by
  have budget : ((appendLeafBranches k t).order : ℕ)≤p := by simpa [Nat.add_comm] using hk
  have h := ho (appendLeafBranches k t) budget
  have wt : (b ⬝ᵥ normTree A (appendLeafBranches k t)) = probe A b k (normTree A t) := by
    rw [normTree_appendLeafBranches,row_apply]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  have factor : (b ⬝ᵥ normTree A (appendLeafBranches k t)) =
      (((appendLeafBranches k t).forestFactorial : ℕ):R) * (b ⬝ᵥ Φ (appendLeafBranches k t) A) := by
    simp only [normTree,dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  have h1 : (((appendLeafBranches k t).order : ℕ) : R) *
      (b ⬝ᵥ normTree A (appendLeafBranches k t)) = 1 := by
    rw [factor,← mul_assoc]
    simpa only [factorial,PNat.mul_coe,Nat.cast_mul] using h
  rwa [wt,order_appendLeafBranches,Nat.add_comm (t.order:ℕ) k] at h1

theorem forestFactorial_isUnit {A : Matrix ι ι R} {b : ι → R} {p : ℕ}
    (ho : HasOrder A b p) (t : FiniteRootedTree) (ht : (t.order:ℕ)≤p) :
    IsUnit (((t.forestFactorial : ℕ) : R)) := by
  have hf : IsUnit ((t.factorial : ℕ) : R) := ho.factorial_isUnit t ht
  rw [factorial,PNat.mul_coe,Nat.cast_mul] at hf
  exact isUnit_of_mul_isUnit_right hf

/-- The actual tree column span at grade j, using the reviewed Φ itself. -/
def treeSpace (A : Matrix ι ι R) (j : ℕ) : Submodule R (ι → R) :=
  Submodule.span R { v | ∃ t : FiniteRootedTree, (t.order:ℕ)≤j+1 ∧ v=Φ t A }

theorem Φ_mem_treeSpace (A : Matrix ι ι R) (t : FiniteRootedTree) {j : ℕ}
    (ht : (t.order:ℕ)≤j+1) : Φ t A∈treeSpace A j :=
  Submodule.subset_span ⟨t,ht,rfl⟩

theorem treeSpace_mono (A : Matrix ι ι R) {j k : ℕ} (h : j≤k) :
    treeSpace A j≤treeSpace A k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,ht,rfl⟩
  exact Φ_mem_treeSpace A t (by omega)

theorem mat_treeSpace (A : Matrix ι ι R) (j : ℕ) :
    treeSpace A j≤(treeSpace A (j+1)).comap (mat A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,ht,rfl⟩
  change mat A (Φ t A)∈treeSpace A (j+1)
  have e : mat A (Φ t A)=Φ (.leaf ◂ t) A := by simp
  rw [e]
  exact Φ_mem_treeSpace A _ (by simp only [order,PNat.add_coe,PNat.one_coe];omega)

theorem diag_treeSpace (A : Matrix ι ι R) (j : ℕ) :
    treeSpace A j≤(treeSpace A (j+1)).comap (diag (nodes A)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,ht,rfl⟩
  change diag (nodes A) (Φ t A)∈treeSpace A (j+1)
  have e : diag (nodes A) (Φ t A)=Φ (t ◂ .leaf) A := by
    ext i
    simp [mul_comm]
  rw [e]
  exact Φ_mem_treeSpace A _ (by simp only [order,PNat.add_coe,PNat.one_coe];omega)

end RKResearch.Certified.Graded
