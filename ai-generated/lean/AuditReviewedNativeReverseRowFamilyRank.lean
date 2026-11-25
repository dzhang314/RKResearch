import RKCert.ReviewedNative.ReverseRowFamilyRank
import RKCert.ReviewedNative.PhysicalSupportCensus

open RKResearch Module
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.PhysicalCensus
open scoped BigOperators Classical Matrix

variable {K α : Type*} [Field K] {s j n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

example (label : Fin s → α) (w : Fin s → K) (a : α) :
    reverseRowFamily (labelIndicator (K := K) label) w a =
      ∑ i : Fin s, if label i = a then w i else 0 := by
  classical
  change row (labelIndicator (K := K) label a) w = _
  rw [row_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : label i = a <;> simp [labelIndicator, ha]

example (H : MeasuredReverseCapacity A b j n) (label : Fin s → α)
    {U : Submodule K (Fin s → K)} (inside : U ≤ back A b n)
    (balanced : U ≤ LinearMap.ker (reverseRowFamily (labelIndicator (K := K) label))) :
    finrank K ((back A b n).map (reverseRowFamily (labelIndicator (K := K) label))) ≤
      finrank K (back A b 0) + n - finrank K U ∧
    (finrank K ((back A b n).map (reverseRowFamily (labelIndicator (K := K) label))) = 0 ↔
      ∀ a, labelIndicator (K := K) label a ∈ treeSpace A j) :=
  ⟨H.row_family_rank_le_deficit (labelIndicator (K := K) label) inside balanced,
    H.row_family_rank_eq_zero_iff (labelIndicator (K := K) label)⟩

#print axioms RKResearch.Certified.Graded.Reverse.MeasuredReverseCapacity.row_family_rank_identity
