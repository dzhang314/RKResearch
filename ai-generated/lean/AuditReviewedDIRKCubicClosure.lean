import RKCert.ReviewedNative.DIRKCubicChronology
open RKResearch RKResearch.Certified.Graded
open scoped Matrix

#print axioms HeadFiber.headInput_mat
#print axioms HeadFiber.five_dirty_three_donor_impossible
#print axioms HeadFiber.Signature.fold_volterra_headInput
#print axioms HeadFiber.no_short_clean_contrast
#print axioms HeadFiber.cubic_amplitude_nonzero_at_origin
#print axioms HeadFiber.dirk_C2_first_clean_clock
#print axioms HeadFiber.dirty_pivot_test
#print axioms HeadFiber.first_clean_taps_not_three
#print axioms HeadFiber.two_clock_separating_primitive
#print axioms HeadFiber.dirk_C2_no_cubic_head
#print axioms dirk_grade_six_surplus_of_C2_of_grade_three_escape

example {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} (lower : A.IsLowerTriangular)
    (order : HasOrder 8 A b) (quadratic : monomialStageDefect A 1=0)
    (escape : ¬ (zeroSpace A 3).map (diag (nodes A)) ≤ zeroSpace A 3) :
    Module.finrank K (zeroSpace A 3)+4 ≤ Module.finrank K (zeroSpace A 6) :=
  dirk_grade_six_surplus_of_C2_of_grade_three_escape lower order (by decide) quadratic escape
