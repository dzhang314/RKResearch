module

import RKCert.ReviewedNative.PaidClockLocalRank

open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

section
variable {K : Type*} [Field K] {s p i j n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

example (H : PaidClockCapacityStaircase A b j n) (positive : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    clockLocal (nodes A) (primitiveBack A b k) =
      clockLocal (nodes A) (annih (treeSpace A j)) :=
  (paid_clock_local_rank_of_staircase H positive).stablePart k hk hkn

example (H : PaidClockCapacityStaircase A b j n) (positive : 1 ≤ n) :
    finrank K (clockLocal (nodes A) (annih (treeSpace A j))) ≤ finrank K (back A b 0) + 1 ∧
    (finrank K (clockLocal (nodes A) (annih (treeSpace A j))) = finrank K (back A b 0) + 1 ↔
      (primitiveBack A b 1).map (diag (nodes A)) ≤ primitiveBack A b 1) := by
  have h := paid_clock_local_rank_of_staircase H positive
  exact ⟨h.rankCap, h.rankExactIff⟩

example [CharZero K] (ha : ∀ a d, a ≤ d → A a d = 0) (ho : HasOrder p A b)
    (positive : 1 ≤ n) (pay : j + n + 2 ≤ p)
    (capacity : s ≤ finrank K (treeSpace A j) + finrank K (back A b 0) + n)
    (nextPay : i + (n + 1) + 2 ≤ p)
    (tight : s < finrank K (treeSpace A i) + finrank K (back A b 0) + n + (n + 2) / 2) :
    PaidClockLocalRank A b j n :=
  paid_clock_local_rank_of_heights (i := i) ha ho positive pay capacity nextPay tight

end

#print axioms RKResearch.Certified.Graded.Reverse.paid_clock_local_rank_of_staircase
#print axioms RKResearch.Certified.Graded.Reverse.paid_clock_local_rank_of_heights
