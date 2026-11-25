module

public import RKResearch.OrderConditions
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! # A local row payment on adjacent finite layers

The stage type is a finite sigma type of fibres indexed by depth.
Masking a matrix to the unique preceding fibre leaves one ordinary
dot product. This transports one paid row and one literal tree graft.
There is no coordinate frame, rank assertion, or whole-tree induction.
-/

namespace RKResearch.FiniteSeries.AdjacentLayerRows

open RKResearch
open scoped BigOperators Matrix

variable {D : ℕ} {L : Fin (D+1) → Type*} {R : Type*}

/-- The actual coordinates of a column lying in one prescribed fibre. -/
def layerSlice (v : Sigma L → R) (h : Fin (D+1)) : L h → R :=
  fun j => v ⟨h, j⟩

@[simp] theorem layerSlice_apply (v : Sigma L → R) (h : Fin (D+1)) (j : L h) :
    layerSlice v h j = v ⟨h, j⟩ := rfl

variable [∀ h, Fintype (L h)]

/-- No casts across fibres: split the sum and keep the unique paid fibre. -/
theorem sum_eq_layer [AddCommMonoid R] (f : Sigma L → R) (h : Fin (D+1))
    (zero : ∀ k : Fin (D+1), k ≠ h → ∀ j : L k, f ⟨k, j⟩ = 0) :
    (∑ j, f j) = ∑ j : L h, f ⟨h, j⟩ := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_eq_single_of_mem h (Finset.mem_univ h)
  intro k _ ne
  exact Finset.sum_eq_zero (fun j _ => zero k ne j)

section MatrixRows

variable [CommSemiring R]

/-- A strict matrix built by discarding every nonadjacent source. The raw
matrix may compute its proposed row separately on each source fibre. -/
def adjacentMask (A : Matrix (Sigma L) (Sigma L) R) :
    Matrix (Sigma L) (Sigma L) R :=
  fun i j => if (j.1 : ℕ)+1 = (i.1 : ℕ) then A i j else 0

theorem adjacentMask_on (A : Matrix (Sigma L) (Sigma L) R) (i j : Sigma L)
    (h : (j.1 : ℕ)+1 = (i.1 : ℕ)) : adjacentMask A i j = A i j :=
  if_pos h

theorem adjacentMask_off (A : Matrix (Sigma L) (Sigma L) R) (i j : Sigma L)
    (h : (j.1 : ℕ)+1 ≠ (i.1 : ℕ)) : adjacentMask A i j = 0 :=
  if_neg h

/-- In any one-step causal matrix, a receiving row is exactly its ordinary
dot product on the specified parent fibre. -/
theorem mulVec_eq_on_parent (A : Matrix (Sigma L) (Sigma L) R)
    (off : ∀ i j : Sigma L, (j.1 : ℕ)+1 ≠ (i.1 : ℕ) → A i j = 0)
    (v : Sigma L → R) (i : Sigma L) (h : Fin (D+1))
    (parent : (h : ℕ)+1 = (i.1 : ℕ)) :
    (A *ᵥ v) i = layerSlice (A i) h ⬝ᵥ layerSlice v h := by
  change (∑ j : Sigma L, A i j * v j) = ∑ j : L h, A i ⟨h, j⟩ * v ⟨h, j⟩
  apply sum_eq_layer (fun j => A i j * v j) h
  intro k ne j
  have away : (k : ℕ)+1 ≠ (i.1 : ℕ) :=
    fun e => ne (Fin.ext (Nat.add_right_cancel (e.trans parent.symm)))
  rw [off i ⟨k, j⟩ away, zero_mul]

/-- On that fibre the mask does not alter the designated raw row. -/
theorem mulVec_adjacentMask_eq_on_parent (A : Matrix (Sigma L) (Sigma L) R)
    (v : Sigma L → R) (i : Sigma L) (h : Fin (D+1))
    (parent : (h : ℕ)+1 = (i.1 : ℕ)) :
    (adjacentMask A *ᵥ v) i = layerSlice (A i) h ⬝ᵥ layerSlice v h := by
  rw [mulVec_eq_on_parent (adjacentMask A) (adjacentMask_off A) v i h parent]
  have eq : layerSlice (adjacentMask A i) h = layerSlice (A i) h := by
    funext j
    exact adjacentMask_on A i ⟨h, j⟩ parent
  rw [eq]

/-- A prescribed action of the parent row extends to the physical masked
matrix whenever the actual input agrees on that parent fibre. -/
theorem mulVec_adjacentMask_eq_of_paid (A : Matrix (Sigma L) (Sigma L) R)
    (v : Sigma L → R) (i : Sigma L) (h : Fin (D+1))
    (parent : (h : ℕ)+1 = (i.1 : ℕ)) {x : L h → R} {z : R}
    (agree : layerSlice v h = x)
    (paid : layerSlice (A i) h ⬝ᵥ x = z) : (adjacentMask A *ᵥ v) i = z := by
  rw [mulVec_adjacentMask_eq_on_parent A v i h parent, agree, paid]

/-- The initial fibre has no predecessor. -/
theorem mulVec_adjacentMask_eq_zero_first (A : Matrix (Sigma L) (Sigma L) R)
    (v : Sigma L → R) (i : Sigma L) (first : (i.1 : ℕ) = 0) :
    (adjacentMask A *ᵥ v) i = 0 := by
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  have off : (j.1 : ℕ)+1 ≠ (i.1 : ℕ) := by
    rw [first]
    exact Nat.succ_ne_zero _
  rw [adjacentMask_off A i j off, zero_mul]

/-- A readout already supported on one fibre, for example the terminal
fibre of an unrolling, is unchanged by taking the row there. -/
theorem dotProduct_eq_on_layer (b v : Sigma L → R) (h : Fin (D+1))
    (off : ∀ i : Sigma L, i.1 ≠ h → b i = 0) :
    b ⬝ᵥ v = layerSlice b h ⬝ᵥ layerSlice v h := by
  change (∑ j : Sigma L, b j * v j) = ∑ j : L h, b ⟨h, j⟩ * v ⟨h, j⟩
  apply sum_eq_layer (fun j => b j * v j) h
  intro k ne j
  rw [off ⟨k, j⟩ ne, zero_mul]

/-- One literal graft transfers using the receiving base value and one
paid action of its parent branch. Height/order accounting is external:
this statement proves neither any global agreement nor any source rank. -/
theorem phi_graft_eq_of_parent {ι : Type*} [Fintype ι]
    (M : Matrix ι ι R) (A : Matrix (Sigma L) (Sigma L) R)
    (base branch : FiniteRootedTree) (i : Sigma L) (k : ι) (h : Fin (D+1))
    (parent : (h : ℕ)+1 = (i.1 : ℕ))
    (base_eq : Φ base (adjacentMask A) i = Φ base M k)
    {x : L h → R} (branch_eq : layerSlice (Φ branch (adjacentMask A)) h = x)
    (paid : layerSlice (A i) h ⬝ᵥ x = (M *ᵥ Φ branch M) k) :
    Φ (.butcherProduct base branch) (adjacentMask A) i =
      Φ (.butcherProduct base branch) M k := by
  change Φ base (adjacentMask A) i * ((adjacentMask A) *ᵥ Φ branch (adjacentMask A)) i =
    Φ base M k * (M *ᵥ Φ branch M) k
  rw [base_eq, mulVec_adjacentMask_eq_of_paid A _ i h parent branch_eq paid]

end MatrixRows

end RKResearch.FiniteSeries.AdjacentLayerRows
