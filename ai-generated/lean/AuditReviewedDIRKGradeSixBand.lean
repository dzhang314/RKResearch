import RKCert.ReviewedNative.DIRKGradeSixBand
open RKResearch RKResearch.Certified.Graded
open scoped Matrix
#print axioms clock_function_mem
#print axioms paid_failed_clock_blocks
#print axioms dirk_inclusive_hermite_family
#print axioms dirk_forward_invariant_outgoing
#print axioms dirk_forward_invariant_incoming
#print axioms dirk_unit_band_of_no_grade_six_surplus
#print axioms dirk_grade_six_surplus_of_invariant_grade

example {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}
    {b : Fin s → K} (order : RKResearch.HasOrder 15 A b) (lower : A.IsLowerTriangular)
    (lastClosed : (zeroSpace A 6).map (diag (nodes A)) ≤ zeroSpace A 6) :
    Module.finrank K (zeroSpace A 3) + 4 ≤ Module.finrank K (zeroSpace A 6) :=
  dirk_grade_six_surplus_of_invariant_grade lower order (by decide) (j:=6)
    (by decide) (by decide) lastClosed
