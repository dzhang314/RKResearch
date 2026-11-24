module

public import RKCert.ReviewedNative.ERKOrderTwelvePureExclusion

public section

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.ERK12 Polynomial

namespace RKResearch.Certified.Graded.AuditERK12Pure

theorem physical_cap_forces_nonzero_leak {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 12 A b) (cap : s+1≤17) :
    s+1=17 ∧ ∃ U z α Q R, RankTwoFourProfile A U z α Q R ∧ α≠0 :=
  ⟨(saturation_of_order ha ho cap).size,actual_nonzero_leak_profile_at_cap ha ho cap⟩

#print axioms pure_profile_primitive_zero
#print axioms exclude_pure_rank_two_four
#print axioms actual_nonzero_leak_profile_at_cap
#print axioms physical_cap_forces_nonzero_leak

end RKResearch.Certified.Graded.AuditERK12Pure

