module
import RKCert.ReviewedNative.ERKOrderTwelveTerminalBand

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.ERK12 Module

section AtTheActualCap
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i j, i≤j → A i j=0) (h : HasOrder A b 12) (cap : s+1≤17)

example : s+1=17 ∧ b (Fin.last s)≠0 ∧ nodes A (Fin.last s)=1 ∧
    finrank K (zeroSpace A 5)=5 ∧ finrank K (zeroSpace A 6)=6 := by
  have S := saturation_of_order ha h cap
  exact ⟨S.size,S.terminal.live,S.terminalClock,S.f5,S.f6⟩

example : finrank K (treeSpace A 7)=14 ∧ finrank K (treeSpace A 8)=15 ∧
    finrank K (treeSpace A 9)=16 ∧ back A b 1=annih (treeSpace A 9) := by
  have S := saturation_of_order ha h cap
  have T := terminal_band ha h S
  have R := reverse_seven_nine ha h S T
  exact ⟨T.e7Rank,R.e8Rank,R.e9Rank,R.back1⟩

example : escape7 A=zeroAt (zeroSpace A 7) (Fin.last s) :=
  (terminal_band ha h (saturation_of_order ha h cap)).cut
end AtTheActualCap

#print axioms paid_sum_cauchy
#print axioms coeff_separated_two_endpoints
#print axioms saturation_of_order
#print axioms exists_order_twelve_head
#print axioms grade_five_zero_at_terminal
#print axioms grade_six_zero_at_terminal
#print axioms terminal_band
#print axioms exists_order_twelve_head_at_seven
#print axioms reverse_seven_nine
