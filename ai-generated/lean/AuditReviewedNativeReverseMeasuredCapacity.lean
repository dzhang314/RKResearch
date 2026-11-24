import RKCert.ReviewedNative.ReverseMeasuredCapacity
import RKCert.ReviewedNative.EndpointAdjoint

open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

variable {K : Type*} [Field K] {s p j n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

-- Audit the exact capacity, the two full-flag identifications, and both
-- separate measured ranks, at arbitrary paid order over an arbitrary field.
example (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b)
    (pay : j + n + 2 ≤ p)
    (cap : s ≤ finrank K (treeSpace A j) + finrank K (back A b 0) + n) :
    s = finrank K (treeSpace A j) + finrank K (back A b 0) + n ∧
    back A b n = annih (treeSpace A j) ∧
    primitiveBack A b n = annih (treeSpace A j) ∧
    (∀ k ≤ n, back A b k = primitiveBack A b k ∧
      finrank K (back A b k) = finrank K (back A b 0) + k ∧
      finrank K (primitiveBack A b k) = finrank K (back A b 0) + k) := by
  let H := reverse_capacity_paid_measured ha ho pay cap
  exact ⟨H.stageCount, H.backFull, H.primitiveFull, H.flagExact⟩

-- Audit that an actual nonzero first seed is admissible: its measured
-- initial rank is one, and it contributes one to both paid flag ranks.
example (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b)
    (pay : j + n + 2 ≤ p) (first : firstSeed A b ≠ 0)
    (cap : s ≤ finrank K (treeSpace A j) + 1 + n) {k : ℕ} (hk : k ≤ n) :
    back A b k = primitiveBack A b k ∧
      finrank K (back A b k) = 1 + k ∧
      finrank K (primitiveBack A b k) = 1 + k := by
  have dim0 := first_dim_one first
  have measured : s ≤ finrank K (treeSpace A j) + finrank K (back A b 0) + n := by
    rw [dim0]
    exact cap
  have H := (reverse_capacity_paid_measured ha ho pay measured).flagExact k hk
  rw [dim0] at H
  exact H

#print axioms RKResearch.Certified.Graded.Reverse.reverse_capacity_paid_measured
