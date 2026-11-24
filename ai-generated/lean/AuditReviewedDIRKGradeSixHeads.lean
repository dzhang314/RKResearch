import RKCert.ReviewedNative.DIRKGradeSixHeads
open RKResearch RKResearch.Certified.Graded
open scoped Matrix
#print axioms HeadFiber.more_escape_sites
#print axioms HeadFiber.localized_mem
#print axioms HeadFiber.core_mul
#print axioms HeadFiber.disjoint_rep
#print axioms HeadFiber.multiplier_polynomial
#print axioms dirk_grade_six_head_at_four
#print axioms dirk_grade_six_head_at_three

example {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}
    {b : Fin s → K} (ho : HasOrder A b 15) (ha : A.IsLowerTriangular)
    (bad : ¬ Module.finrank K (zeroSpace A 3)+4 ≤ Module.finrank K (zeroSpace A 6))
    (inv : (zeroSpace A 3).map (diag (nodes A)) ≤ zeroSpace A 3) :
    ∃ w : Fin s → K, 4 ≤ (HeadFiber.escapeSites (nodes A) w (zeroSpace A 3)).card := by
  obtain ⟨w,_,count,_⟩ := dirk_grade_six_head_at_four ha ho (by decide) bad inv
  exact ⟨w,count⟩
