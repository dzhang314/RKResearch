module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Fin.Rev

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # First nonzero antidiagonal: a standard determinant seed

This leaf does not need Mathlib's separate Matrix.Rank artifact. -/
namespace RKResearch.Certified.Graded.HankelAntiTriangularRank

open Matrix

variable {K : Type*} [Field K]

/-- Reversing columns makes the first nonzero antidiagonal the
ordinary diagonal of a lower triangular matrix. -/
theorem det_ne_zero_of_first_antidiagonal {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (zero : ∀ i j : Fin n, i.val+j.val < n-1 → M i j=0)
    (live : ∀ i j : Fin n, i.val+j.val = n-1 → M i j≠0) :
    M.det≠0 := by
  let N := M.submatrix id Fin.revPerm
  have tri : N.IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    change M i (Fin.rev j)=0
    apply zero
    rw [Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
    omega
  have diag (i : Fin n) : N.diag i≠0 := by
    change M i (Fin.rev i)≠0
    apply live
    rw [Fin.val_rev]
    have hi := i.isLt
    omega
  have det : N.det ≠ 0 := (Matrix.IsLowerTriangular.det_ne_zero_iff tri).mpr diag
  intro bad
  apply det
  change (M.submatrix id Fin.revPerm).det = 0
  rw [Matrix.det_permute',bad,mul_zero]

end RKResearch.Certified.Graded.HankelAntiTriangularRank
