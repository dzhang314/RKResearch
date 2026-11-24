import RKCert.ReviewedNative.StagePadding

open RKResearch RKResearch.Certified.StagePadding

-- At exactly 26, a future native exclusion would directly imply the 27-stage bound.
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (no26 : ∀ (T : Matrix (Fin 26) (Fin 26) K) (w : Fin 26 → K),
      (∀ i j, i ≤ j → T i j = 0) → HasOrder 17 T w → False)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : 27 ≤ s :=
  strict_stages_gt_of_exact_exclusion no26 ha ho

-- The analogous lower-triangular dispatcher accepts the full width-20 class.
example {R : Type*} [CommSemiring R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (no20 : ∀ (T : Matrix (Fin 20) (Fin 20) R) (w : Fin 20 → R),
      T.IsLowerTriangular → HasOrder 15 T w → False)
    (ha : A.IsLowerTriangular) (ho : HasOrder 15 A b) : 21 ≤ s :=
  lower_stages_gt_of_exact_exclusion no20 ha ho

-- A genuinely new diagonal entry is zero.
example {R : Type*} [CommSemiring R] {s n : ℕ}
    {A : Matrix (Fin s) (Fin s) R} (h : s < n) :
    zeroPadMatrix A n (⟨s,h⟩ : Fin n) ⟨s,h⟩ = 0 :=
  zeroPadMatrix_tail_row A le_rfl

#print axioms RKResearch.Certified.StagePadding.hasOrder_zeroPad_iff
#print axioms RKResearch.Certified.StagePadding.zeroPadMatrix_strict_iff
#print axioms RKResearch.Certified.StagePadding.zeroPadMatrix_lower_iff
#print axioms RKResearch.Certified.StagePadding.zeroPadMatrix_nonzero_diagonal_iff
#print axioms RKResearch.Certified.StagePadding.strict_stages_gt_of_exact_exclusion
#print axioms RKResearch.Certified.StagePadding.lower_stages_gt_of_exact_exclusion
