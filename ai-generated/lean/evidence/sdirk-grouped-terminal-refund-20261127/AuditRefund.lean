import RKCert.ReviewedNative.GroupedTerminalRefund

open RKResearch.Certified.GroupedTerminalRefund

#check clockFrame_injective
#check refund_rank
#check refunded_word_steps
#check four_block_floor
#check no_thirty_three
#check no_twenty_five
#check saturated_terminal_count
#print axioms clockFrame_injective
#print axioms refund_rank
#print axioms refunded_word_steps
#print axioms four_block_floor
#print axioms no_thirty_three
#print axioms no_twenty_five
#print axioms saturated_terminal_count

example (n t old d : ℕ) (ht : t ≤ n) (hn : 8 ≤ n)
    (hrefund : t ≤ d + (n - 8)) (hpacket : 12 + d ≤ old) :
    ¬ (15 + old + (n - t) - 1 ≤ 33) := by
  have := no_thirty_three n t old d ht hn hrefund hpacket
  omega

example (n t old d : ℕ) (ht : t ≤ n) (hn : 7 ≤ n)
    (hrefund : t ≤ d + (n - 7)) (hpacket : 9 + d ≤ old) :
    ¬ (11 + old + (n - t) - 1 ≤ 25) := by
  have := no_twenty_five n t old d ht hn hrefund hpacket
  omega
