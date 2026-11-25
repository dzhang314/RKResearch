import RKCert.ReviewedNative.MinimalDefectTwoSeedTail
import RKCert.ReviewedNative.PaidEndpointClock

open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s p q : ℕ} {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}

/-- Typed downstream demonstration: the two literal zero tests replace
the extra grade-three chain premise, not any paid endpoint hypothesis. -/
theorem audit_paid_endpoint_interior_of_two_seed_zeros
    (strict : ∀ i j, i≤j → A i j=0) (order : HasOrder p A b)
    (q₃ : 3≤q) (q₁₀ : q≤10) (pay : 2*q≤p)
    (r : finrank K (zeroSpace A q)=q-1)
    {t i : Fin (s+1)} (one : nodes A t=1) (live : b t≠0)
    (coord : coordinate (K:=K) t∈treeSpace A q) (off : i≠t) (cn : nodes A i≠0)
    (g0 : monomialStageDefect A 1 i=0) (h0 : mat A (monomialStageDefect A 1) i=0) :
    nodes A i∈Set.Ioo (0:K) 1 := by
  obtain ⟨J,H⟩ := paid_endpoint_clock_of_coordinate (q:=q) strict order
    (by omega) q₁₀ pay one live coord
  have clean := (minimal_defect_clean_iff_two_actual_seeds strict order
    pay r q₃ le_rfl i).mpr ⟨g0,h0⟩
  exact H.clean_clock_interior off cn clean

#print axioms RKResearch.Certified.Graded.clean_iff_line_clock_chain
#print axioms RKResearch.Certified.Graded.minimal_defect_clock_tail_of_grade_three
#print axioms RKResearch.Certified.Graded.minimal_defect_clock_tail_of_single_quadratic_live_clock
#print axioms RKResearch.Certified.Graded.minimal_defect_clean_iff_two_actual_seeds
#print axioms audit_paid_endpoint_interior_of_two_seed_zeros
