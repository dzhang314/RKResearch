import RKCert.ReviewedNative.ReverseLocalized

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse Module

#print axioms normalized_residual_apply
#print axioms greatest_reflected_pivot
#print axioms reflected_live_avoid
#print axioms localized_reverse_chart_of_ranks
#print axioms localized_reverse_rows_of_chart
#print axioms localized_reverse_rows_impossible
#print axioms localized_native_reverse_impossible

example {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder p A b)
    (pay : 10 ≤ p) (seedZero : firstSeed A b = 0)
    (ranks : ∀ n ≤ 4, finrank K (back A b n) = n)
    (nc2 : ¬ (back A b 2).map (diag (reflectedClock A)) ≤ back A b 2)
    (nc3 : ¬ (back A b 3).map (diag (reflectedClock A)) ≤ back A b 3)
    (h2 : normalizedResidual A b 2 ∈ back A b 2)
    (h3 : normalizedResidual A b 3 ∈ back A b 3) :
    ¬ (back A b 1).map (diag (reflectedClock A)) ≤ back A b 1 :=
  localized_native_reverse_impossible ha ho pay seedZero ranks nc2 nc3 h2 h3
