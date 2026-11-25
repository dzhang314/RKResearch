module

import RKCert.ReviewedNative.ShortenedWeightedDefectCharge

open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open scoped BigOperators Classical

section
variable {K : Type*} [Field K] {s p j g n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

example (H : PaidClockCapacityStaircase A b j n) (positive : 1 ≤ n) (ho : HasOrder p A b)
    (S : Finset K) (pay : j + g + S.card ≤ p) :
    ((∑ x : ClockSite (nodes A),
        finrank K (clockFiberColumns (nodes A) (shortenedWeightedDefect A b g S) x)) ≤
      finrank K (clockLocal (nodes A) (annih (treeSpace A j)))) ∧
    ((∑ x : ClockSite (nodes A),
        finrank K (clockFiberColumns (nodes A) (shortenedWeightedDefect A b g S) x)) ≤
      finrank K (back A b 0) + 1) :=
  ⟨paid_shortenedWeightedDefect_clock_charge (j := j) (g := g) ho S pay,
    paid_shortenedWeightedDefect_clock_charge_of_staircase (g := g) H positive ho S pay⟩

example (H : PaidClockCapacityStaircase A b j n) (positive : 1 ≤ n) (ho : HasOrder p A b)
    (S : Finset K) (pay : j + g + S.card ≤ p) :
    finrank K (clockWeightedDefect A b g) ≤
      finrank K ((clockWeightedDefect A b g).map (clockComplementRestrict (nodes A) S)) +
        (finrank K (back A b 0) + 1) :=
  paid_weightedDefect_rank_le_punctured_add_of_staircase (g := g) H positive ho S pay

end

#print axioms RKResearch.Certified.Graded.Reverse.paid_shortenedWeightedDefect_clock_charge_of_staircase
#print axioms RKResearch.Certified.Graded.Reverse.paid_weightedDefect_rank_le_punctured_add_of_staircase
