module

public import RKCert.ReviewedNative.ERKOrderTwelveRankThree

public section

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.ERK12
open Module

namespace RKResearch.Certified.Graded.AuditERK12Cubic

/-- No extra algebraic, chronological, or stage-count premises are
hidden in the two remaining native width-seventeen branches. -/
theorem actual_cap_has_rank_two_branches {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 12 A b) (cap : s+1≤17) :
    ∃ U w, ForwardStaircase A 2 U w ∧
      zeroSpace A 2≤U ∧ zeroSpace A 3≤U ∧
      (finrank K (zeroSpace A 4)=3 ∨ finrank K (zeroSpace A 4)=4) := by
  let S := saturation_of_order ha ho cap
  let T := terminal_band ha ho S
  obtain ⟨r,U,w,H⟩ := forward_staircase ha ho S
  obtain ⟨rfl,branches⟩ := remaining_rank_two_branches ha ho S T H
  exact ⟨U,w,H,grade_two_in_core ha ho S T H,grade_three_in_core ha ho S T H,branches⟩

#print axioms buffered_two_leaks
#print axioms grade_eight_no_double_leak
#print axioms grade_three_in_core
#print axioms exclude_paid_cubic_profile
#print axioms exclude_three_four
#print axioms remaining_rank_two_branches
#print axioms actual_cap_has_rank_two_branches

end RKResearch.Certified.Graded.AuditERK12Cubic

