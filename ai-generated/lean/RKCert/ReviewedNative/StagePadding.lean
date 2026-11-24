module

public import RKCert.ReviewedNative.GradedPrefix
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-! # Zero-weight isolated stages do not change reviewed RK order

Everything uses the literal reviewed matrix and rooted-tree recursion.
The old indices retain their order, and the new indices are appended.
Both strict and ordinary lower triangularity are preserved. Nonzero
diagonal conditions are not preserved at a genuinely larger width. -/
namespace RKResearch.Certified.StagePadding

open RKResearch RKResearch.Certified.Graded
open scoped Matrix

variable {R : Type*} [CommSemiring R] {s n p : ℕ}

/-- Prefix-preserving zero extension when `s ≤ n`. -/
def zeroPadVec (v : Fin s → R) (n : ℕ) : Fin n → R :=
  fun i => if h : i.val < s then v ⟨i.val,h⟩ else 0

/-- Zero-fill both the new rows and the new columns. -/
def zeroPadMatrix (A : Matrix (Fin s) (Fin s) R) (n : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  fun i => if h : i.val < s then zeroPadVec (A ⟨i.val,h⟩) n else 0

@[simp] theorem zeroPadVec_castLE (v : Fin s → R) (h : s ≤ n) (i : Fin s) :
    zeroPadVec v n (Fin.castLE h i) = v i := by
  simp [zeroPadVec,i.isLt]

theorem zeroPadVec_tail (v : Fin s → R) {i : Fin n} (h : s ≤ i.val) :
    zeroPadVec v n i = 0 := by
  simp [zeroPadVec,not_lt_of_ge h]

@[simp] theorem zeroPadMatrix_castLE (A : Matrix (Fin s) (Fin s) R) (h : s ≤ n) (i j : Fin s) :
    zeroPadMatrix A n (Fin.castLE h i) (Fin.castLE h j) = A i j := by
  simp [zeroPadMatrix,i.isLt,zeroPadVec,j.isLt]

theorem zeroPadMatrix_tail_row (A : Matrix (Fin s) (Fin s) R) {i j : Fin n}
    (h : s ≤ i.val) : zeroPadMatrix A n i j = 0 := by
  simp [zeroPadMatrix,not_lt_of_ge h]

theorem zeroPadMatrix_tail_col (A : Matrix (Fin s) (Fin s) R) {i j : Fin n}
    (h : s ≤ j.val) : zeroPadMatrix A n i j = 0 := by
  by_cases hi : i.val < s
  · simp [zeroPadMatrix,hi,zeroPadVec,not_lt_of_ge h]
  · simp [zeroPadMatrix,hi]

@[simp] theorem prefix_zeroPadMatrix (A : Matrix (Fin s) (Fin s) R) (h : s ≤ n) :
    prefixMatrix (zeroPadMatrix A n) h = A := by
  ext i j
  exact zeroPadMatrix_castLE A h i j

private theorem zeroPattern_iff {A : Matrix (Fin s) (Fin s) R} (h : s ≤ n)
    (P : ℕ → ℕ → Prop) :
    (∀ i j : Fin n, P i.val j.val → zeroPadMatrix A n i j = 0) ↔
    (∀ i j : Fin s, P i.val j.val → A i j = 0) := by
  constructor
  · intro z i j hij
    simpa only [zeroPadMatrix_castLE] using z (Fin.castLE h i) (Fin.castLE h j) hij
  · intro z i j hij
    by_cases hi : i.val < s
    · by_cases hj : j.val < s
      · simpa only [zeroPadMatrix,zeroPadVec,dite_eq_left hi,dite_eq_left hj] using
          z ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij
      · exact zeroPadMatrix_tail_col A (Nat.le_of_not_gt hj)
    · exact zeroPadMatrix_tail_row A (Nat.le_of_not_gt hi)

theorem zeroPadMatrix_strict_iff {A : Matrix (Fin s) (Fin s) R} (h : s ≤ n) :
    (∀ i j : Fin n, i ≤ j → zeroPadMatrix A n i j = 0) ↔
    (∀ i j : Fin s, i ≤ j → A i j = 0) :=
  zeroPattern_iff h (· ≤ ·)

theorem zeroPadMatrix_lower_iff {A : Matrix (Fin s) (Fin s) R} (h : s ≤ n) :
    (zeroPadMatrix A n).IsLowerTriangular ↔ A.IsLowerTriangular := by
  have e := zeroPattern_iff (A:=A) h (· < ·)
  exact ⟨fun z {_ _} x => e.mp (fun _ _ y => z y) _ _ x,
    fun z {_ _} x => e.mpr (fun _ _ y => z y) _ _ x⟩

/-- Entrywise restriction of an arbitrary matrix-vector product. The original
matrix need not be triangular: the upper-right zero block is already built in. -/
theorem zeroPadMatrix_mulVec_castLE (A : Matrix (Fin s) (Fin s) R) (h : s ≤ n)
    (v : Fin n → R) (i : Fin s) :
    (zeroPadMatrix A n *ᵥ v) (Fin.castLE h i) = (A *ᵥ (v ∘ Fin.castLE h)) i := by
  unfold Matrix.mulVec dotProduct
  rw [←sum_prefix_zero_tail h (fun j => zeroPadMatrix A n (Fin.castLE h i) j * v j)
    (fun j hj => by rw [zeroPadMatrix_tail_col A hj,zero_mul])]
  simp only [zeroPadMatrix_castLE,Function.comp_apply]

/-- Tree columns agree on the original physical indices, with no
condition or assertion about the appended entries of the leaf column. -/
theorem Φ_zeroPadMatrix_castLE (A : Matrix (Fin s) (Fin s) R) (h : s ≤ n)
    (t : FiniteRootedTree) (i : Fin s) :
    Φ t (zeroPadMatrix A n) (Fin.castLE h i) = Φ t A i := by
  induction t generalizing i with
  | leaf => rfl
  | butcherProduct t u ht hu =>
    have eq : Φ u (zeroPadMatrix A n) ∘ Fin.castLE h = Φ u A := funext hu
    rw [Φ,Φ,Pi.mul_apply,Pi.mul_apply,ht i,zeroPadMatrix_mulVec_castLE,eq]

/-- All elementary weights are unchanged, since the new weights vanish. -/
theorem dotProduct_Φ_zeroPad (A : Matrix (Fin s) (Fin s) R) (b : Fin s → R)
    (h : s ≤ n) (t : FiniteRootedTree) :
    zeroPadVec b n ⬝ᵥ Φ t (zeroPadMatrix A n) = b ⬝ᵥ Φ t A := by
  unfold dotProduct
  rw [←sum_prefix_zero_tail h (fun j => zeroPadVec b n j * Φ t (zeroPadMatrix A n) j)
    (fun j hj => by rw [zeroPadVec_tail b hj,zero_mul])]
  simp only [zeroPadVec_castLE,Φ_zeroPadMatrix_castLE]

/-- No conversion or normalization of the reviewed order definition is used. -/
theorem hasOrder_zeroPad_iff {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : s ≤ n) : HasOrder p (zeroPadMatrix A n) (zeroPadVec b n) ↔ HasOrder p A b := by
  unfold HasOrder
  simp only [dotProduct_Φ_zeroPad A b h]

/-- A nonzero diagonal can survive zero padding only if no stage is appended. -/
theorem zeroPadMatrix_nonzero_diagonal_iff {A : Matrix (Fin s) (Fin s) R} (h : s ≤ n) :
    (∀ i : Fin n, zeroPadMatrix A n i i ≠ 0) ↔ s = n ∧ ∀ i : Fin s, A i i ≠ 0 := by
  constructor
  · intro nz
    have e : s = n := by
      by_contra ne
      have lt : s < n := lt_of_le_of_ne h ne
      exact nz ⟨s,lt⟩ (zeroPadMatrix_tail_row A le_rfl)
    exact ⟨e,fun i => by simpa only [zeroPadMatrix_castLE] using nz (Fin.castLE h i)⟩
  · rintro ⟨rfl,nz⟩ i
    simpa only [Fin.castLE_refl,zeroPadMatrix_castLE] using
      (show zeroPadMatrix A s (Fin.castLE h i) (Fin.castLE h i) ≠ 0 by
        simpa only [zeroPadMatrix_castLE] using nz i)

/-- Exclusion at exactly `n` stages rules out all explicit widths at most `n`. -/
theorem strict_stages_gt_of_exact_exclusion
    (exclude : ∀ (T : Matrix (Fin n) (Fin n) R) (w : Fin n → R),
      (∀ i j, i ≤ j → T i j = 0) → HasOrder p T w → False)
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (hu : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) : n < s := by
  by_contra! h
  exact exclude _ _ ((zeroPadMatrix_strict_iff h).mpr hu) ((hasOrder_zeroPad_iff h).mpr ho)

/-- The same conclusion for the full lower-triangular class, not a subclass
which requires a nonsingular diagonal. -/
theorem lower_stages_gt_of_exact_exclusion
    (exclude : ∀ (T : Matrix (Fin n) (Fin n) R) (w : Fin n → R),
      T.IsLowerTriangular → HasOrder p T w → False)
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (hu : A.IsLowerTriangular) (ho : HasOrder p A b) : n < s := by
  by_contra! h
  exact exclude _ _ ((zeroPadMatrix_lower_iff h).mpr hu) ((hasOrder_zeroPad_iff h).mpr ho)

end RKResearch.Certified.StagePadding
