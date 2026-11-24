import RKCert.ReviewedNative.ERKOrder15TerminalEight

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

/-- A consumer with just the prescribed ordered-field, native order,
strict matrix and width assumptions. -/
theorem audit_native_order15_early_terminal {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {s : ℕ} {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    {b : Fin (s+1)→K} (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder A b 15)
    (cap : s+1≤22) :
    ∃ (a : ℕ) (G : K[X]) (U : Submodule K (Fin (s+1)→K)) (w : Fin (s+1)→K),
      Order15PaidStaircase A b a G 2 U w ∧ finrank K (zeroSpace A 4)=4 ∧
      firstSeed A b=0 ∧ coordinate (K:=K) (Fin.last s)∈treeSpace A 8 ∧
      coordinate (K:=K) (Fin.last s)∉treeSpace A 7 :=
  order15_ordered_terminal_chart ha ho cap

#print axioms RKResearch.Certified.Graded.clock_chain_drop_of_next_unpaid
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.early_two_head_payment
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.four_eq_core_head
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.three_core_eq
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.no_three_dimensional_four
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.ordinary_four_rank
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.paid_quartic_profile_of_absent
#print axioms RKResearch.Certified.Graded.Order15PaidStaircase.terminal_eight_rank_two
#print axioms RKResearch.Certified.Graded.order15_ordered_terminal_chart
#print axioms RKResearch.Certified.Graded.no_rank_three_clock_core_at_order_ten
#print axioms audit_native_order15_early_terminal
