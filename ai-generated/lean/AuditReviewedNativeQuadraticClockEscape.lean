import RKCert.ReviewedNative.QuadraticClockEscape
import RKCert.ReviewedNative.MinimalDefectClean

open RKResearch Module RKResearch.Certified.Graded

noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p q : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

theorem audit_minimal_clean_of_two_dirty_clocks
    (strict : ∀ i j, i≤j → A i j=0) (order : HasOrder p A b)
    (q₂ : 2≤q) (pay : 2*q≤p) (rank : finrank K (zeroSpace A q)=q-1)
    {i j : Fin s} (hi : monomialStageDefect A 1 i≠0)
    (hj : monomialStageDefect A 1 j≠0) (different : nodes A i≠nodes A j)
    (k : Fin s) : (∀ f∈zeroSpace A q, f k=0) ↔ monomialStageDefect A 1 k=0 :=
  minimal_defect_clean_iff_quadratic_zero strict order pay rank
    (minimal_defect_baseF3_of_two_quadratic_live_clocks strict order pay rank hi hj different)
    q₂ le_rfl k

#print axioms RKResearch.Certified.Graded.clock_line_escape_iff_two_live_clocks
#print axioms RKResearch.Certified.Graded.grade_three_chain_of_two_quadratic_live_clocks
#print axioms RKResearch.Certified.Graded.minimal_defect_baseF3_of_two_quadratic_live_clocks
#print axioms audit_minimal_clean_of_two_dirty_clocks
