module

import RKCert.ReviewedNative.ClockFamilyRank

open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open scoped BigOperators Classical

section
variable {K α : Type*} [Field K] {s : ℕ}

example (c : Fin s → K) (Q : α → Submodule K (Fin s → K)) (F : Finset α) :
    clockFamilyRank c Q F = ∑ x : ClockSite c, finrank K (clockFiberColumns c (F.sup Q) x) := by
  unfold clockFamilyRank
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact congrArg (fun L : Submodule K (ClockFiber c x → K) => finrank K L)
    (clockFamilyFiber_eq_columns_sup c Q F x)

example (c : Fin s → K) (Q : α → Submodule K (Fin s → K)) (F : Finset α) (a : α) :
    clockFamilyRank c Q (insert a F) = clockFamilyRank c Q F +
      (∑ x : ClockSite c, (finrank K (clockFiberColumns c (Q a) x) -
        finrank K ↥(clockFiberColumns c (Q a) x ⊓ clockFamilyFiber c Q F x :
          Submodule K (ClockFiber c x → K)))) :=
  clockFamilyRank_insert c Q F a

example (c : Fin s → K) (Q : α → Submodule K (Fin s → K))
    {F G : Finset α} (h : F ⊆ G) (a : α) :
    clockFamilyGain c Q G a ≤ clockFamilyGain c Q F a :=
  clockFamilyGain_antitone c Q h a

variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {j n : ℕ}

example (H : PaidClockCapacityStaircase A b j n) (positive : 1 ≤ n)
    (Q : α → Submodule K (Fin s → K)) (F : Finset α)
    (separatelyPaid : ∀ a ∈ F, Q a ≤ clockLocal (nodes A) (annih (treeSpace A j))) :
    clockFamilyRank (nodes A) Q F ≤ finrank K (back A b 0) + 1 :=
  clockFamilyRank_le_of_staircase H positive Q F separatelyPaid

end

#print axioms RKResearch.Certified.Graded.Reverse.clockFamilyFiber_eq_columns_sup
#print axioms RKResearch.Certified.Graded.Reverse.clockFamilyRank_insert
#print axioms RKResearch.Certified.Graded.Reverse.clockFamilyGain_antitone
#print axioms RKResearch.Certified.Graded.Reverse.clockFamilyRank_le_of_staircase
