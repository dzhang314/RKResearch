module

public import RKCert.ReviewedNative.ERKOrderTwelveRankTwoFour

public section

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.ERK12 Polynomial

namespace RKResearch.Certified.Graded.AuditERK12RankTwoFour

theorem actual_square_profile_or_quartic_factor {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 12 A b) (cap : s+1≤17) :
    ∃ U z α Q R, RankTwoFourProfile A U z α Q R ∧
      (α≠0 ∨ (terminalMesh6=R*Q ∧ R.natDegree=4 ∧ Q.natDegree=2 ∧
        ∀ i, z i≠0 → z i=R.eval (nodes A i))) := by
  obtain ⟨U,z,α,Q,R,H,split⟩ := actual_rank_two_four_profile ha ho cap
  refine ⟨U,z,α,Q,R,H,?_⟩
  exact split.imp id (fun h => H.pure_factor h.1)

#print axioms grade_eight_single_leak
#print axioms rank_two_four_profile
#print axioms RankTwoFourProfile.pure_factor
#print axioms actual_rank_two_four_profile
#print axioms actual_square_profile_or_quartic_factor

end RKResearch.Certified.Graded.AuditERK12RankTwoFour

