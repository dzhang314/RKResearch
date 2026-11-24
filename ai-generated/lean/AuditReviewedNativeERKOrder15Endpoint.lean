import RKCert.ReviewedNative.ERKOrder15NativeEndpoint

open RKResearch RKResearch.Certified RKResearch.Certified.Graded

theorem audit_native_erk15_stage_bound {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder A b 15) : 23≤s :=
  native_explicit_order_fifteen_at_least_twenty_three ha ho

#print axioms terminal_eight_zeros_defects
#print axioms marked_five_parts
#print axioms marked_five_terminal_probe
#print axioms Order15PaidStaircase.terminal_head_first_powers
#print axioms square_shifts_of_ordinary_head
#print axioms Order15PaidStaircase.ten_head_band_terminal_probe
#print axioms Order15PaidStaircase.terminal_ghost_decompose
#print axioms Order15PaidStaircase.three_terminal_squares
#print axioms Order15PaidStaircase.actual_terminal_divisor
#print axioms Order15TerminalDivisor.paid_knot
#print axioms Order15TerminalDivisor.origin_nonzero
#print axioms Order15TerminalDivisor.omitted_knot
#print axioms Order15PaidStaircase.native_terminal_impossible
#print axioms native_explicit_order_fifteen_at_least_twenty_three
#print axioms audit_native_erk15_stage_bound
