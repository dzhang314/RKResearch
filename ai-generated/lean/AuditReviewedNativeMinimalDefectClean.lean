import RKCert.ReviewedNative.MinimalDefectClean

open RKResearch Module RKResearch.Certified.Graded

noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p q : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

theorem audit_minimal_midpoint_clean_row
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder p A b)
    (q₂ : 2≤q) (pay : 2*q≤p) (rank : finrank K (zeroSpace A q)=q-1)
    (baseF3 : 3≤q → zeroSpace A 3=
      RKCert.OneEscape.chain (diag (nodes A)) ⊥ (monomialStageDefect A 1) 2)
    (i : Fin s) (vanishes : monomialStageDefect A 1 i=0)
    (f : Fin s→K) (hf : f∈zeroSpace A q) : f i=0 :=
  (minimal_defect_clean_iff_quadratic_zero ha ho pay rank baseF3 q₂ le_rfl i).mpr vanishes f hf

#print axioms RKResearch.Certified.Graded.minimal_defect_clock_chain
#print axioms RKResearch.Certified.Graded.clean_iff_quadratic_zero_of_clock_chain
#print axioms RKResearch.Certified.Graded.minimal_defect_clean_iff_quadratic_zero
#print axioms audit_minimal_midpoint_clean_row
