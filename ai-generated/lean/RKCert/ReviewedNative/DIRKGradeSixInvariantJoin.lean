module

public import RKCert.ReviewedNative.DIRKGradeSixJoin
public import RKCert.ReviewedNative.DIRKGradeSixBand

public section

/-! # Composition with the already checked native clock-invariance branch

The arithmetic join is unconditional on the branch proved by the independent
grade-six worker. This small adapter does not assert that every tableau is in
that branch, nor solve either remaining head exclusion.
-/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- If any one of F₄, F₅, F₆ is invariant under the physical clock, the
stronger stage count is already proved at every order p ≥ 12. -/
theorem dirk_uniform_of_invariant_middle_grade (ha : A.IsLowerTriangular)
    (ho : HasOrder A b p) (hp : 12 ≤ p) {j : ℕ} (lo : 4 ≤ j) (hi : j ≤ 6)
    (inv : (zeroSpace A j).map (diag (nodes A)) ≤ zeroSpace A j) : p+(p-1)/2-2 ≤ s :=
  dirk_uniform_of_grade_six ha ho hp
    (dirk_grade_six_surplus_of_invariant_grade ha ho (by omega) lo hi inv)

/-- Any original tableau below the stronger floor must give *all* three
unit growth steps and *all* three noninvariant clock levels, not merely
an unspecified failure of the desired rank. -/
theorem dirk_short_forces_grade_six_band (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    (hp : 12 ≤ p) (short : s < p+(p-1)/2-2) :
    (∀ j, 3≤j → j<6 → finrank K (zeroSpace A (j+1)) = finrank K (zeroSpace A j)+1) ∧
    (∀ j, 4≤j → j≤6 → ¬(zeroSpace A j).map (diag (nodes A)) ≤ zeroSpace A j) :=
  dirk_unit_band_of_no_grade_six_surplus ha ho (by omega)
    (fun six => (Nat.not_le_of_gt short) (dirk_uniform_of_grade_six ha ho hp six))

end RKResearch.Certified.Graded.Reverse
