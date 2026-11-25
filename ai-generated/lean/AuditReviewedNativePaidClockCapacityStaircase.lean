module

import RKCert.ReviewedNative.PaidClockCapacityStaircase

open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

section
variable {K : Type*} [Field K] [CharZero K] {s p i j n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

-- The tested interface is exactly the generic two-height theorem.
example (ha : ∀ u v, u ≤ v → A u v = 0) (ho : RKResearch.HasOrder p A b)
    (pay : j+n+2 ≤ p)
    (capacity : s ≤ finrank K (treeSpace A j) + finrank K (back A b 0) + n)
    (nextPay : i+(n+1)+2 ≤ p)
    (tight : s < finrank K (treeSpace A i) + finrank K (back A b 0) + n + (n+2)/2) :
    PaidClockCapacityStaircase A b j n :=
  paid_clock_capacity_staircase_of_heights ha ho (i:=i) pay capacity nextPay tight

example (h : PaidClockCapacityStaircase A b j n) (m : ℕ) (hm : m+1 ≤ n) :
    back A b (n-m) = annih (treeSpace A (j+m)) ∧
    primitiveBack A b (n-m) = annih (treeSpace A (j+m)) :=
  ⟨(h.forwardCapacity m hm).backFull, (h.forwardCapacity m hm).primitiveFull⟩

example (h : PaidClockCapacityStaircase A b j n) (k : ℕ) (hk : 2 ≤ k) (kn : k < n) :
    (primitiveBack A b k).map (mat A.transpose) ≤ primitiveBack A b k ⊔
      (primitiveBack A b k).map (diag (reflectedClock A)) :=
  (h.reverseUnit k hk kn).2

end

#print axioms paid_clock_capacity_staircase_of_heights
