import RKCert.ReviewedNative.SingleQuadraticClockGradeThree

open RKResearch Module RKResearch.Certified.Graded

noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p q : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

theorem audit_single_quadratic_clock_clean
    (strict : ∀ i j, i≤j → A i j=0) (order : HasOrder p A b)
    (q₃ : 3≤q) (pay : 2*q≤p) (rank : finrank K (zeroSpace A q)=q-1)
    (a : K) (single : ∀ j, monomialStageDefect A 1 j≠0 → nodes A j=a)
    (i : Fin s) : (∀ f∈zeroSpace A 3, f i=0) ↔
      monomialStageDefect A 1 i=0 ∧ mat A (monomialStageDefect A 1) i=0 :=
  (minimal_grade_three_of_single_quadratic_live_clock strict order q₃ pay rank a single).clean i

#print axioms RKResearch.Certified.Graded.clean_iff_two_vector_span
#print axioms RKResearch.Certified.Graded.mat_quadratic_defect_outside_clock_stable_line
#print axioms RKResearch.Certified.Graded.grade_three_of_single_quadratic_live_clock
#print axioms RKResearch.Certified.Graded.minimal_grade_three_of_single_quadratic_live_clock
#print axioms audit_single_quadratic_clock_clean
