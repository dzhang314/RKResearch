module

public import RKCert.ReviewedNative.ERKOrderTwelveRankTwoThree

public section

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.ERK12
open Module

namespace RKResearch.Certified.Graded.AuditERK12RankTwoThree

theorem physical_cap_fourth_rank_four {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder A b 12) (cap : s+1≤17) :
    s+1=17 ∧ finrank K (zeroSpace A 4)=4 := by
  obtain ⟨_,_,_,h⟩ := only_rank_two_four_at_cap ha ho cap
  exact ⟨(saturation_of_order ha ho cap).size,h⟩

#print axioms fourth_grade_eq_core_of_rank_two_three
#print axioms exclude_two_three
#print axioms only_rank_two_four_at_cap
#print axioms physical_cap_fourth_rank_four

end RKResearch.Certified.Graded.AuditERK12RankTwoThree

