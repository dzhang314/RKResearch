module

public import RKCert.ReviewedNative.ReverseFlag

public section

/-! # Exact measured reverse capacity for the native flags -/

namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module

variable {K : Type*} [Field K] {s : ℕ}

/-- Exact reverse capacity on the original tableau. The top two-row and
all-monomial flags are the full annihilator; at earlier grades only their
equality to each other and their measured ranks are asserted. -/
structure MeasuredReverseCapacity
    (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (j n : ℕ) : Prop where
  stageCount : s = finrank K (treeSpace A j) + finrank K (back A b 0) + n
  backFull : back A b n = annih (treeSpace A j)
  primitiveFull : primitiveBack A b n = annih (treeSpace A j)
  flagExact : ∀ k ≤ n, back A b k = primitiveBack A b k ∧
    finrank K (back A b k) = finrank K (back A b 0) + k ∧
    finrank K (primitiveBack A b k) = finrank K (back A b 0) + k

variable {p j n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Saturation with the true initial reverse dimension, with no vanishing
first-seed or terminal hypothesis. -/
theorem reverse_capacity_paid_measured
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b)
    (pay : j + n + 2 ≤ p)
    (capacity : s ≤ finrank K (treeSpace A j) + finrank K (back A b 0) + n) :
    MeasuredReverseCapacity A b j n := by
  have stages : s = finrank K (treeSpace A j) + finrank K (back A b 0) + n :=
    le_antisymm capacity (backward_count ha ho j n pay)
  have dimAnn := finrank_annih (treeSpace A j)
  rw [Fintype.card_fin] at dimAnn
  have annRank : finrank K (annih (treeSpace A j)) = finrank K (back A b 0) + n := by
    omega
  have backToPrimitive := back_le_primitiveBack (A := A) (b := b) n
  have primitiveToAnn := primitiveBack_annih ho j n pay
  have growTop := back_finrank ha ho n (by omega)
  have exactBack : back A b n = annih (treeSpace A j) :=
    Submodule.eq_of_le_of_finrank_le (backToPrimitive.trans primitiveToAnn) (by omega)
  have exactPrimitive : primitiveBack A b n = annih (treeSpace A j) := by
    apply le_antisymm primitiveToAnn
    rw [← exactBack]
    exact backToPrimitive
  have topRank : finrank K (primitiveBack A b n) = finrank K (back A b 0) + n := by
    rw [exactPrimitive, annRank]
  refine ⟨stages, exactBack, exactPrimitive, ?_⟩
  intro k hk
  have gain := primitiveBack_interval ha ho k (n - k) (by omega)
  rw [show k + (n - k) = n by omega, topRank] at gain
  have low := back_finrank ha ho k (by omega)
  have inc := back_le_primitiveBack (A := A) (b := b) k
  have mono := Submodule.finrank_mono inc
  have equal : back A b k = primitiveBack A b k :=
    Submodule.eq_of_le_of_finrank_le inc (by omega)
  exact ⟨equal, by omega, by omega⟩

end RKResearch.Certified.Graded.Reverse
