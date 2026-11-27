import RKCert.ReviewedNative.ProtectedTerminalRefund

open RKResearch.Certified.ProtectedTerminalRefund

#check protected_mem_low_at_exact_count
#check clockFrame_surjective_square
#check vanish_supported_discrepancy
#check discrepancy_sum
#check kill_site_commutator
#check exact_overlap_counts
#print axioms protected_mem_low_at_exact_count
#print axioms clockFrame_surjective_square
#print axioms vanish_supported_discrepancy
#print axioms discrepancy_sum
#print axioms kill_site_commutator
#print axioms exact_overlap_counts

example (n t old d : ℕ) (ht : t ≤ n) (hn : 8 ≤ n) (hlow : 12 ≤ old)
    (hrefund : t-1 ≤ d + (n-8)) (hpacket : 12+d ≤ old)
    (hbudget : old+(n-t) ≤ 19) :
    old = 12+d ∧ old+(n-t) = 19 ∧ n-t ≤ 7 := by
  exact exact_overlap_counts 6 n t old d 12 ht hn hlow hrefund hpacket hbudget

example (n t old d : ℕ) (ht : t ≤ n) (hn : 7 ≤ n) (hlow : 9 ≤ old)
    (hrefund : t-1 ≤ d + (n-7)) (hpacket : 9+d ≤ old)
    (hbudget : old+(n-t) ≤ 15) :
    old = 9+d ∧ old+(n-t) = 15 ∧ n-t ≤ 6 := by
  exact exact_overlap_counts 5 n t old d 9 ht hn hlow hrefund hpacket hbudget
