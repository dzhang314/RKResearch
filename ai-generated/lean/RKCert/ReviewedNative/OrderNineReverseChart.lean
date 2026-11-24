module

public import RKCert.ReviewedNative.TerminalCapacity
public import RKCert.ReviewedNative.ReverseInvariantBudget

@[expose] public section

/-! # Native physical reverse chart at order nine and full fifth rank -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module

variable {K : Type*} [Field K] {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

theorem orderNine_rank_five_full (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder A b 9) (rank5 : finrank K (treeSpace A 5) = 10) :
    firstSeed A b = 0 ∧ nodes A (Fin.last 11) = 1 ∧
    coordinate (K:=K) (Fin.last 11) ∈ treeSpace A 5 ∧
    coordinate (K:=K) (Fin.last 11) ∉ treeSpace A 4 ∧
    back A b 2 = annih (treeSpace A 5) ∧
    (∀ U : Submodule K (Fin 12 → K), U ≤ annih (treeSpace A 5) →
      (∀ v ∈ U, mat A.transpose v ∈ U) →
      (∀ v ∈ U, diag (reflectedClock A) v ∈ U) → U = ⊥) := by
  have last := lastActive_of_odd_floor ha ho (q:=4) (by decide) (by decide) (by decide)
  have cap : 12 ≤ finrank K (treeSpace A 5)+2 := by omega
  obtain ⟨z,atOne,backFull,in5⟩ := reverse_capacity_terminal ha ho (j:=5) (n:=2)
    (by decide) cap last
  exact ⟨z,atOne,in5 _ le_rfl,endpoint_coordinate_out ha ho (q:=4) (by decide) _ last.live atOne,
    backFull,no_joint_invariant_of_paid_capacity ha ho (j:=5) (n:=2) (by decide) cap⟩

end RKResearch.Certified.Graded.Reverse
